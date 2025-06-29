// Lean compiler output
// Module: Lake.Build.Common
// Imports: Lake.Config.Monad Lake.Util.JsonObject Lake.Build.Target.Fetch Lake.Build.Actions Lake.Build.Job
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
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_read(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFromJsonFileOutputHash(lean_object*);
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(lean_object*, lean_object*);
lean_object* l_Lake_compileO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildO___closed__0;
static lean_object* l_Lake_buildO___lam__2___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildSharedLib___lam__3___closed__0;
LEAN_EXPORT lean_object* l_Lake_writeFileHash(lean_object*, uint64_t, lean_object*);
static lean_object* l_Lake_instFromJsonBuildMetadata___closed__0;
lean_object* l_Lake_instMonadLiftLakeMBuildTOfPure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepList___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___at___Lean_rewriteManualLinksCore_rw_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildFileAfterDep___redArg___lam__0___closed__0;
static lean_object* l_List_mapTR_loop___at___Lake_formatCycle___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1_spec__1___closed__0;
lean_object* l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileHash(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatCycle___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_addLeanTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_remove_file(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5___closed__0;
lean_object* l_Lake_Job_mapM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
static lean_object* l_Lake_buildStaticLib___closed__0;
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0_spec__0(lean_object*);
lean_object* lean_get_set_stdout(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__10;
lean_object* l_Lake_compileSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_byte_array_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_collectList___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_buildLeanO___lam__0___closed__1;
static lean_object* l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata___closed__0____x40_Lake_Build_Common___hyg_178_;
LEAN_EXPORT lean_object* l_Lake_inputTextFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lake_computeTextFileHash(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lake_inputDir_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__14;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lake_inputDir_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__3;
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_metadata(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchLocalArtifact___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPureTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l_Lake_platformTrace___closed__1;
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_System_FilePath_exeExtension;
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_platformTrace___closed__2;
lean_object* l_Lake_EStateT_instPure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__0;
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__13;
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0___boxed(lean_object*);
static lean_object* l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__3___closed__0;
lean_object* l_IO_FS_DirEntry_path(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__6;
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at_____private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178__spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata___closed__2____x40_Lake_Build_Common___hyg_178_;
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfExists(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata___closed__3____x40_Lake_Build_Common___hyg_178_;
lean_object* l_Lake_CacheMap_insertCore(uint64_t, lean_object*, lean_object*);
static lean_object* l_Lake_buildArtifactUnlessUpToDate___closed__8;
lean_object* l_Lake_Hash_ofString_x3f(lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0;
static lean_object* l_Lake_buildArtifactUnlessUpToDate___closed__11;
LEAN_EXPORT lean_object* l_Lake_instToJsonPUnit__lake___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EquipT_instMonad___redArg(lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepArray___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instToStringString___lam__0___boxed(lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lake_inputDir_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_readTraceFile_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Dynlib_dir_x3f(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonPUnit__lake___lam__0___boxed(lean_object*);
lean_object* l_Lake_BuildTrace_mix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfExists___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1463_(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildArtifactUnlessUpToDate___closed__0;
lean_object* l_Lake_compileExe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at_____private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178__spec__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_crlfToLf(lean_object*);
static lean_object* l_Lake_buildArtifactUnlessUpToDate___closed__6;
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_serializeInputs_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_IO_FS_writeBinFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveArtifactsUsing_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
extern lean_object* l_Lake_sharedLibExt;
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofHash(uint64_t);
static lean_object* l_Lake_readTraceFile___closed__0;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_platformTrace;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__2;
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_writeFileHash___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_inputBinFile___redArg___closed__1;
static lean_object* l_Lake_buildArtifactUnlessUpToDate___closed__3;
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__3_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__3;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__0;
lean_object* l_UInt64_fromJson_x3f(lean_object*);
lean_object* l_Lake_createParentDirs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildLeanO_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Array_foldlMUnsafe_fold___at___Lake_buildLeanO_spec__0(lean_object*, size_t, size_t, uint64_t);
lean_object* l_Lake_EStateT_instFunctor___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceJobM;
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___Lake_inputTextFile_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepArray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__11;
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__8;
extern lean_object* l_ByteArray_empty;
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchLocalArtifact___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__12;
LEAN_EXPORT lean_object* l_Lake_readTraceFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfExists___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata___closed__1____x40_Lake_Build_Common___hyg_178_;
LEAN_EXPORT lean_object* l_Lake_writeTraceFile_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__1;
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFromJsonBuildMetadata;
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instAlternativeOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0(lean_object*);
static uint64_t l_Lake_platformTrace___closed__0;
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Lake_JobM_runFetchM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_collectArray___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_platformTrace___closed__3;
LEAN_EXPORT lean_object* l_Lake_buildO___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instResolveArtifactsFileOutputHashArtifactOfMonadLakeEnvOfMonadLiftTBaseIOOfMonad___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static uint8_t l_Lake_buildAction___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_resolveArtifactsUsing_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_instDataKindFilePath;
static lean_object* l_Lake_inputBinFile___redArg___lam__1___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildArtifactUnlessUpToDate___closed__7;
LEAN_EXPORT lean_object* l_Lake_buildAction___at___Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lake_buildSharedLib___closed__0;
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofHash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lake_inputDir_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildO___lam__2___closed__2;
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instAlternativeELogTOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildArtifactUnlessUpToDate___closed__1;
lean_object* l_Lake_JobState_merge(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at_____private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178__spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Lake_CacheMap_get_x3f(uint64_t, lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepList___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__7;
static lean_object* l_Lake_inputBinFile___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_serializeInputs(lean_object*);
lean_object* l_Lake_copyFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lake_inputDir_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5_spec__5_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepList___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheFileHash(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArtifactTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveArtifactsUsing_x3f___at___Lake_buildArtifactUnlessUpToDate_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__17;
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_platformTrace___closed__5___boxed__const__1;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata___closed__4____x40_Lake_Build_Common___hyg_178_;
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__6;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_toJson___at_____private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178__spec__4_spec__4(size_t, size_t, lean_object*);
static lean_object* l_Lake_buildArtifactUnlessUpToDate___closed__13;
static lean_object* l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_toJson___at_____private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178__spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_platformTrace___closed__4;
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfExists___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArtifactTrace(lean_object*, lean_object*, uint64_t, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Prod_fromJson_x3f___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5_spec__5_spec__5___closed__0;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_buildLeanO_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_toJson___at_____private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178__spec__0_spec__1(size_t, size_t, lean_object*);
lean_object* l_Lake_BuildTrace_nil(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonFileOutputHash(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instResolveArtifactsFileOutputHashArtifactOfMonadLakeEnvOfMonadLiftTBaseIOOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint64_t);
lean_object* lean_get_set_stderr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EquipT_instFunctor___redArg(lean_object*);
static lean_object* l_Lake_buildLeanSharedLib___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0;
static lean_object* l_Lake_instToJsonBuildMetadata___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__15;
LEAN_EXPORT lean_object* l_Lake_fetchLocalArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_serializeInputs___boxed(lean_object*);
lean_object* l_Lake_Cache_getArtifact_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
static lean_object* l_Lake_checkHashUpToDate___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildArtifactUnlessUpToDate___closed__9;
LEAN_EXPORT lean_object* l_Lake_buildAction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildLeanO___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_toJson___at_____private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178__spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at_____private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178__spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_readTraceFile___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lake_inputDir_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lake_writeFileHash___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lake_inputDir_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildLeanO_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepArray___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__1;
static lean_object* l_Lake_buildStaticLib___lam__1___closed__0;
static lean_object* l_Prod_toJson___at___Array_toJson___at_____private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178__spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__0;
static lean_object* l_Lake_resolveArtifactsUsing_x3f___redArg___closed__0;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_serializeInputs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate_doBuild(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonFileOutputHash___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPureTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Option_beqOption___redArg____x40_Init_Data_Option_Basic___hyg_160_(lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0_spec__0___closed__0;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lake_Hash_load_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_filterMapM___at___Lake_inputDir_spec__1___closed__0;
LEAN_EXPORT lean_object* l_Lake_resolveArtifactsUsing_x3f(lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___Lean_Name_getString_x21_spec__0(lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputFile(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg___lam__0(lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__9;
LEAN_EXPORT lean_object* l_Lake_instResolveArtifactsFileOutputHashArtifactOfMonadLakeEnvOfMonadLiftTBaseIOOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lake_EquipT_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_serializeInputs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_inputDir_spec__0(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonPUnit__lake;
static lean_object* l_Lake_buildArtifactUnlessUpToDate___closed__10;
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildFileUnlessUpToDate_x27___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepList___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lake_inputDir_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Option_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__3_spec__3___closed__0;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_instDataKindDynlib;
static lean_object* l_Lake_buildFileAfterDepList___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___Lake_inputBinFile_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildLeanO_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Artifact_trace(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildLeanO_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_exit(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instResolveArtifactsFileOutputHashArtifactOfMonadLakeEnvOfMonadLiftTBaseIOOfMonad___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_writeTraceFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepList___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_addPureTrace___redArg___closed__0;
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeTraceFile___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__4;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lake_formatCycle___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1_spec__1(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__4;
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lake_instMonadLiftTOfMonadLift__lake___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stdin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5_spec__5(lean_object*);
lean_object* l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__5;
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepArray___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__18;
LEAN_EXPORT lean_object* l_Lake_writeTraceFile_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_LeanInstall_ccLinkFlags(uint8_t, lean_object*);
static lean_object* l_Lake_buildArtifactUnlessUpToDate___closed__5;
LEAN_EXPORT lean_object* l_Lake_writeTraceFile___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_JobAction_merge(uint8_t, uint8_t);
LEAN_EXPORT uint64_t l_Lake_buildO___lam__0(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___at___Lake_envToBool_x3f_spec__1(lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildArtifactUnlessUpToDate___closed__2;
lean_object* l_Lean_bignumToJson(lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveArtifactsUsing_x3f___redArg(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* l_Lake_beqHash____x40_Lake_Build_Trace___hyg_486____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonBuildMetadata;
lean_object* l_String_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_read_dir(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildArtifactUnlessUpToDate___closed__12;
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_inputTextFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_MTime_checkUpToDate___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0;
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__20;
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildLeanO_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lake_compileStaticLib(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveArtifactsUsing_x3f___at___Lake_buildArtifactUnlessUpToDate_spec__0(lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_List_flatMapTR_go___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonPosition____x40_Lean_Data_Lsp_Basic___hyg_226__spec__0(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178_(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lake_inputDir_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_qsort_sort___at___Lake_inputDir_spec__3___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1411_(lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildLeanO___lam__0___closed__2;
lean_object* l_Lake_EStateT_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeTraceFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFromJsonFileOutputHash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_computeBinFileHash(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lake_buildO___lam__2___closed__1;
LEAN_EXPORT uint32_t l_Lake_noBuildCode;
LEAN_EXPORT lean_object* l_Lake_buildO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_inputBinFile___redArg___closed__0;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__5;
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instResolveArtifactsFileOutputHashArtifactOfMonadLakeEnvOfMonadLiftTBaseIOOfMonad___redArg___lam__0(uint64_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__16;
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Cache_artifactPath(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_resolveArtifactsUsing_x3f___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__19;
LEAN_EXPORT lean_object* l_Lake_instFromJsonFileOutputHash___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Prod_toJson___at___Array_toJson___at_____private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178__spec__0_spec__0(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_addPureTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_inputDir_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
static lean_object* l_Lake_formatCycle___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_IO_FS_readBinFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchLocalArtifact(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5_spec__5_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate_doBuild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_System_Platform_target;
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonFileOutputHash___lam__0(uint64_t);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonFileOutputHash___boxed(lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lake_resolveArtifactsUsing_x3f___redArg___closed__1;
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_inputBinFile___redArg___closed__3;
static lean_object* l_Lake_platformTrace___closed__5;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instResolveArtifactsFileOutputHashArtifactOfMonadLakeEnvOfMonadLiftTBaseIOOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_clearFileHash(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheFileHash___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_IO_FS_ordSystemTime____x40_Init_System_IO___hyg_3236_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildArtifactUnlessUpToDate___closed__4;
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__7;
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJson_x3f(lean_object*);
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEIO(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instMonadWorkspaceJobM___closed__2;
x_2 = l_Lake_instMonadWorkspaceJobM___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lake_instMonadWorkspaceJobM___closed__6;
x_2 = l_Lake_instMonadWorkspaceJobM___closed__5;
x_3 = l_Lake_instMonadWorkspaceJobM___closed__4;
x_4 = l_Lake_instMonadWorkspaceJobM___closed__3;
x_5 = l_Lake_instMonadWorkspaceJobM___closed__8;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instMonadWorkspaceJobM___closed__7;
x_2 = l_Lake_instMonadWorkspaceJobM___closed__9;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instMonadWorkspaceJobM___closed__8;
x_2 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instMonadWorkspaceJobM___closed__8;
x_2 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instMonadWorkspaceJobM___closed__12;
x_2 = l_Lake_instMonadWorkspaceJobM___closed__11;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instMonadWorkspaceJobM___closed__0;
x_2 = l_Lake_instAlternativeELogTOfMonad___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_EStateM_pure), 5, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instMonadWorkspaceJobM___closed__15;
x_2 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instMonadWorkspaceJobM___closed__10;
x_2 = lean_alloc_closure((void*)(l_ReaderT_read), 4, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instMonadWorkspaceJobM___closed__13;
x_2 = l_Lake_instMonadWorkspaceJobM___closed__17;
x_3 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instMonadWorkspaceJobM___closed__13;
x_2 = l_Lake_instMonadWorkspaceJobM___closed__18;
x_3 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instMonadWorkspaceJobM___closed__19;
x_2 = l_Lake_instMonadWorkspaceJobM___closed__16;
x_3 = lean_alloc_closure((void*)(l_Lake_instMonadLiftLakeMBuildTOfPure___redArg___lam__0), 4, 3);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, lean_box(0));
lean_closure_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lake_instMonadWorkspaceJobM___closed__0;
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 4);
lean_dec(x_8);
x_9 = lean_ctor_get(x_3, 3);
lean_dec(x_9);
x_10 = lean_ctor_get(x_3, 2);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_11, 0, x_7);
lean_closure_set(x_11, 1, x_5);
lean_inc(x_5);
lean_inc(x_7);
x_12 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_12, 0, x_7);
lean_closure_set(x_12, 1, x_5);
lean_inc(x_11);
lean_inc(x_7);
x_13 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_13, 0, x_7);
lean_closure_set(x_13, 1, x_11);
lean_inc(x_7);
lean_inc(x_6);
x_14 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_14, 0, x_6);
lean_closure_set(x_14, 1, x_7);
lean_closure_set(x_14, 2, x_5);
x_15 = l_Lake_EStateT_instFunctor___redArg(x_6);
x_16 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_16, 0, x_7);
lean_inc(x_15);
lean_ctor_set(x_3, 4, x_12);
lean_ctor_set(x_3, 3, x_13);
lean_ctor_set(x_3, 2, x_14);
lean_ctor_set(x_3, 1, x_16);
lean_ctor_set(x_3, 0, x_15);
lean_ctor_set(x_1, 1, x_11);
lean_inc(x_15);
x_17 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_17, 0, x_15);
x_18 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_18, 0, x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lake_instMonadWorkspaceJobM___closed__14;
lean_inc(x_1);
x_21 = l_ReaderT_instAlternativeOfMonad___redArg(x_20, x_1);
x_22 = l_ReaderT_instMonad___redArg(x_1);
lean_inc(x_22);
x_23 = l_ReaderT_instAlternativeOfMonad___redArg(x_21, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_ReaderT_instMonad___redArg(x_22);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
lean_inc(x_28);
x_29 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_29, 0, x_28);
x_30 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_30, 0, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_inc(x_26);
x_32 = l_ReaderT_instMonad___redArg(x_26);
x_33 = !lean_is_exclusive(x_26);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_34 = lean_ctor_get(x_26, 1);
lean_dec(x_34);
x_35 = lean_ctor_get(x_26, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
lean_inc(x_37);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_38, 0, x_37);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_39, 0, x_37);
lean_ctor_set(x_26, 1, x_39);
lean_ctor_set(x_26, 0, x_38);
lean_inc(x_26);
x_40 = l_Lake_EquipT_instFunctor___redArg(x_26);
x_41 = !lean_is_exclusive(x_32);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_42 = lean_ctor_get(x_32, 0);
x_43 = lean_ctor_get(x_32, 1);
lean_dec(x_43);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lake_instMonadWorkspaceJobM___closed__20;
lean_inc(x_19);
x_46 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_45, x_19);
x_47 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_46, x_19);
x_48 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(x_48, 0, lean_box(0));
lean_closure_set(x_48, 1, lean_box(0));
lean_closure_set(x_48, 2, lean_box(0));
lean_closure_set(x_48, 3, lean_box(0));
lean_closure_set(x_48, 4, x_47);
lean_inc(x_25);
x_49 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_48, x_25);
x_50 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_49, x_25);
x_51 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_51, 0, lean_box(0));
lean_closure_set(x_51, 1, x_50);
lean_inc(x_31);
x_52 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_51, x_31);
x_53 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_52, x_31);
x_54 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_54, 0, lean_box(0));
lean_closure_set(x_54, 1, x_53);
lean_inc(x_26);
x_55 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_54, x_26);
x_56 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_55, x_26);
x_57 = lean_alloc_closure((void*)(l_Lake_EquipT_lift___boxed), 5, 4);
lean_closure_set(x_57, 0, lean_box(0));
lean_closure_set(x_57, 1, lean_box(0));
lean_closure_set(x_57, 2, lean_box(0));
lean_closure_set(x_57, 3, x_56);
lean_inc(x_40);
x_58 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_57, x_40);
x_59 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_58, x_40);
x_60 = lean_alloc_closure((void*)(l_Lake_JobM_runFetchM), 9, 2);
lean_closure_set(x_60, 0, lean_box(0));
lean_closure_set(x_60, 1, x_59);
lean_inc(x_44);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_61, 0, x_44);
x_62 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_62, 0, x_44);
lean_ctor_set(x_32, 1, x_62);
lean_ctor_set(x_32, 0, x_61);
x_63 = l_Lake_EquipT_instFunctor___redArg(x_32);
x_64 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_60, x_63);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_65 = lean_ctor_get(x_32, 0);
lean_inc(x_65);
lean_dec(x_32);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec(x_65);
x_67 = l_Lake_instMonadWorkspaceJobM___closed__20;
lean_inc(x_19);
x_68 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_67, x_19);
x_69 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_68, x_19);
x_70 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(x_70, 0, lean_box(0));
lean_closure_set(x_70, 1, lean_box(0));
lean_closure_set(x_70, 2, lean_box(0));
lean_closure_set(x_70, 3, lean_box(0));
lean_closure_set(x_70, 4, x_69);
lean_inc(x_25);
x_71 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_70, x_25);
x_72 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_71, x_25);
x_73 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_73, 0, lean_box(0));
lean_closure_set(x_73, 1, x_72);
lean_inc(x_31);
x_74 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_73, x_31);
x_75 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_74, x_31);
x_76 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_76, 0, lean_box(0));
lean_closure_set(x_76, 1, x_75);
lean_inc(x_26);
x_77 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_76, x_26);
x_78 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_77, x_26);
x_79 = lean_alloc_closure((void*)(l_Lake_EquipT_lift___boxed), 5, 4);
lean_closure_set(x_79, 0, lean_box(0));
lean_closure_set(x_79, 1, lean_box(0));
lean_closure_set(x_79, 2, lean_box(0));
lean_closure_set(x_79, 3, x_78);
lean_inc(x_40);
x_80 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_79, x_40);
x_81 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_80, x_40);
x_82 = lean_alloc_closure((void*)(l_Lake_JobM_runFetchM), 9, 2);
lean_closure_set(x_82, 0, lean_box(0));
lean_closure_set(x_82, 1, x_81);
lean_inc(x_66);
x_83 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_83, 0, x_66);
x_84 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_84, 0, x_66);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lake_EquipT_instFunctor___redArg(x_85);
x_87 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_82, x_86);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_26);
x_88 = lean_ctor_get(x_32, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec(x_88);
lean_inc(x_89);
x_90 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_90, 0, x_89);
x_91 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_91, 0, x_89);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
lean_inc(x_92);
x_93 = l_Lake_EquipT_instFunctor___redArg(x_92);
x_94 = lean_ctor_get(x_32, 0);
lean_inc(x_94);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_95 = x_32;
} else {
 lean_dec_ref(x_32);
 x_95 = lean_box(0);
}
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
lean_dec(x_94);
x_97 = l_Lake_instMonadWorkspaceJobM___closed__20;
lean_inc(x_19);
x_98 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_97, x_19);
x_99 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_98, x_19);
x_100 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(x_100, 0, lean_box(0));
lean_closure_set(x_100, 1, lean_box(0));
lean_closure_set(x_100, 2, lean_box(0));
lean_closure_set(x_100, 3, lean_box(0));
lean_closure_set(x_100, 4, x_99);
lean_inc(x_25);
x_101 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_100, x_25);
x_102 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_101, x_25);
x_103 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_103, 0, lean_box(0));
lean_closure_set(x_103, 1, x_102);
lean_inc(x_31);
x_104 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_103, x_31);
x_105 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_104, x_31);
x_106 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_106, 0, lean_box(0));
lean_closure_set(x_106, 1, x_105);
lean_inc(x_92);
x_107 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_106, x_92);
x_108 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_107, x_92);
x_109 = lean_alloc_closure((void*)(l_Lake_EquipT_lift___boxed), 5, 4);
lean_closure_set(x_109, 0, lean_box(0));
lean_closure_set(x_109, 1, lean_box(0));
lean_closure_set(x_109, 2, lean_box(0));
lean_closure_set(x_109, 3, x_108);
lean_inc(x_93);
x_110 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_109, x_93);
x_111 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_110, x_93);
x_112 = lean_alloc_closure((void*)(l_Lake_JobM_runFetchM), 9, 2);
lean_closure_set(x_112, 0, lean_box(0));
lean_closure_set(x_112, 1, x_111);
lean_inc(x_96);
x_113 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_113, 0, x_96);
x_114 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_114, 0, x_96);
if (lean_is_scalar(x_95)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_95;
}
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_116 = l_Lake_EquipT_instFunctor___redArg(x_115);
x_117 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_112, x_116);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_118 = lean_ctor_get(x_1, 1);
x_119 = lean_ctor_get(x_3, 0);
x_120 = lean_ctor_get(x_3, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_3);
lean_inc(x_118);
lean_inc(x_120);
x_121 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_121, 0, x_120);
lean_closure_set(x_121, 1, x_118);
lean_inc(x_118);
lean_inc(x_120);
x_122 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_122, 0, x_120);
lean_closure_set(x_122, 1, x_118);
lean_inc(x_121);
lean_inc(x_120);
x_123 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_123, 0, x_120);
lean_closure_set(x_123, 1, x_121);
lean_inc(x_120);
lean_inc(x_119);
x_124 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_124, 0, x_119);
lean_closure_set(x_124, 1, x_120);
lean_closure_set(x_124, 2, x_118);
x_125 = l_Lake_EStateT_instFunctor___redArg(x_119);
x_126 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_126, 0, x_120);
lean_inc(x_125);
x_127 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
lean_ctor_set(x_127, 2, x_124);
lean_ctor_set(x_127, 3, x_123);
lean_ctor_set(x_127, 4, x_122);
lean_ctor_set(x_1, 1, x_121);
lean_ctor_set(x_1, 0, x_127);
lean_inc(x_125);
x_128 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_128, 0, x_125);
x_129 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_129, 0, x_125);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = l_Lake_instMonadWorkspaceJobM___closed__14;
lean_inc(x_1);
x_132 = l_ReaderT_instAlternativeOfMonad___redArg(x_131, x_1);
x_133 = l_ReaderT_instMonad___redArg(x_1);
lean_inc(x_133);
x_134 = l_ReaderT_instAlternativeOfMonad___redArg(x_132, x_133);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
lean_dec(x_134);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
lean_dec(x_135);
x_137 = l_ReaderT_instMonad___redArg(x_133);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
lean_dec(x_138);
lean_inc(x_139);
x_140 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_140, 0, x_139);
x_141 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_141, 0, x_139);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
lean_inc(x_137);
x_143 = l_ReaderT_instMonad___redArg(x_137);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_144 = x_137;
} else {
 lean_dec_ref(x_137);
 x_144 = lean_box(0);
}
x_145 = lean_ctor_get(x_143, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
lean_dec(x_145);
lean_inc(x_146);
x_147 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_147, 0, x_146);
x_148 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_148, 0, x_146);
if (lean_is_scalar(x_144)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_144;
}
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
lean_inc(x_149);
x_150 = l_Lake_EquipT_instFunctor___redArg(x_149);
x_151 = lean_ctor_get(x_143, 0);
lean_inc(x_151);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_152 = x_143;
} else {
 lean_dec_ref(x_143);
 x_152 = lean_box(0);
}
x_153 = lean_ctor_get(x_151, 0);
lean_inc(x_153);
lean_dec(x_151);
x_154 = l_Lake_instMonadWorkspaceJobM___closed__20;
lean_inc(x_130);
x_155 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_154, x_130);
x_156 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_155, x_130);
x_157 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(x_157, 0, lean_box(0));
lean_closure_set(x_157, 1, lean_box(0));
lean_closure_set(x_157, 2, lean_box(0));
lean_closure_set(x_157, 3, lean_box(0));
lean_closure_set(x_157, 4, x_156);
lean_inc(x_136);
x_158 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_157, x_136);
x_159 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_158, x_136);
x_160 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_160, 0, lean_box(0));
lean_closure_set(x_160, 1, x_159);
lean_inc(x_142);
x_161 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_160, x_142);
x_162 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_161, x_142);
x_163 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_163, 0, lean_box(0));
lean_closure_set(x_163, 1, x_162);
lean_inc(x_149);
x_164 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_163, x_149);
x_165 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_164, x_149);
x_166 = lean_alloc_closure((void*)(l_Lake_EquipT_lift___boxed), 5, 4);
lean_closure_set(x_166, 0, lean_box(0));
lean_closure_set(x_166, 1, lean_box(0));
lean_closure_set(x_166, 2, lean_box(0));
lean_closure_set(x_166, 3, x_165);
lean_inc(x_150);
x_167 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_166, x_150);
x_168 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_167, x_150);
x_169 = lean_alloc_closure((void*)(l_Lake_JobM_runFetchM), 9, 2);
lean_closure_set(x_169, 0, lean_box(0));
lean_closure_set(x_169, 1, x_168);
lean_inc(x_153);
x_170 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_170, 0, x_153);
x_171 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_171, 0, x_153);
if (lean_is_scalar(x_152)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_152;
}
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
x_173 = l_Lake_EquipT_instFunctor___redArg(x_172);
x_174 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_169, x_173);
return x_174;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_175 = lean_ctor_get(x_1, 0);
x_176 = lean_ctor_get(x_1, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_1);
x_177 = lean_ctor_get(x_175, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_175, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 lean_ctor_release(x_175, 2);
 lean_ctor_release(x_175, 3);
 lean_ctor_release(x_175, 4);
 x_179 = x_175;
} else {
 lean_dec_ref(x_175);
 x_179 = lean_box(0);
}
lean_inc(x_176);
lean_inc(x_178);
x_180 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_180, 0, x_178);
lean_closure_set(x_180, 1, x_176);
lean_inc(x_176);
lean_inc(x_178);
x_181 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_181, 0, x_178);
lean_closure_set(x_181, 1, x_176);
lean_inc(x_180);
lean_inc(x_178);
x_182 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_182, 0, x_178);
lean_closure_set(x_182, 1, x_180);
lean_inc(x_178);
lean_inc(x_177);
x_183 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_183, 0, x_177);
lean_closure_set(x_183, 1, x_178);
lean_closure_set(x_183, 2, x_176);
x_184 = l_Lake_EStateT_instFunctor___redArg(x_177);
x_185 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_185, 0, x_178);
lean_inc(x_184);
if (lean_is_scalar(x_179)) {
 x_186 = lean_alloc_ctor(0, 5, 0);
} else {
 x_186 = x_179;
}
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
lean_ctor_set(x_186, 2, x_183);
lean_ctor_set(x_186, 3, x_182);
lean_ctor_set(x_186, 4, x_181);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_180);
lean_inc(x_184);
x_188 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_188, 0, x_184);
x_189 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_189, 0, x_184);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
x_191 = l_Lake_instMonadWorkspaceJobM___closed__14;
lean_inc(x_187);
x_192 = l_ReaderT_instAlternativeOfMonad___redArg(x_191, x_187);
x_193 = l_ReaderT_instMonad___redArg(x_187);
lean_inc(x_193);
x_194 = l_ReaderT_instAlternativeOfMonad___redArg(x_192, x_193);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
lean_dec(x_194);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
lean_dec(x_195);
x_197 = l_ReaderT_instMonad___redArg(x_193);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
lean_dec(x_198);
lean_inc(x_199);
x_200 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_200, 0, x_199);
x_201 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_201, 0, x_199);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
lean_inc(x_197);
x_203 = l_ReaderT_instMonad___redArg(x_197);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_204 = x_197;
} else {
 lean_dec_ref(x_197);
 x_204 = lean_box(0);
}
x_205 = lean_ctor_get(x_203, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
lean_dec(x_205);
lean_inc(x_206);
x_207 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_207, 0, x_206);
x_208 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_208, 0, x_206);
if (lean_is_scalar(x_204)) {
 x_209 = lean_alloc_ctor(0, 2, 0);
} else {
 x_209 = x_204;
}
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
lean_inc(x_209);
x_210 = l_Lake_EquipT_instFunctor___redArg(x_209);
x_211 = lean_ctor_get(x_203, 0);
lean_inc(x_211);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_212 = x_203;
} else {
 lean_dec_ref(x_203);
 x_212 = lean_box(0);
}
x_213 = lean_ctor_get(x_211, 0);
lean_inc(x_213);
lean_dec(x_211);
x_214 = l_Lake_instMonadWorkspaceJobM___closed__20;
lean_inc(x_190);
x_215 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_214, x_190);
x_216 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_215, x_190);
x_217 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(x_217, 0, lean_box(0));
lean_closure_set(x_217, 1, lean_box(0));
lean_closure_set(x_217, 2, lean_box(0));
lean_closure_set(x_217, 3, lean_box(0));
lean_closure_set(x_217, 4, x_216);
lean_inc(x_196);
x_218 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_217, x_196);
x_219 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_218, x_196);
x_220 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_220, 0, lean_box(0));
lean_closure_set(x_220, 1, x_219);
lean_inc(x_202);
x_221 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_220, x_202);
x_222 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_221, x_202);
x_223 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_223, 0, lean_box(0));
lean_closure_set(x_223, 1, x_222);
lean_inc(x_209);
x_224 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_223, x_209);
x_225 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_224, x_209);
x_226 = lean_alloc_closure((void*)(l_Lake_EquipT_lift___boxed), 5, 4);
lean_closure_set(x_226, 0, lean_box(0));
lean_closure_set(x_226, 1, lean_box(0));
lean_closure_set(x_226, 2, lean_box(0));
lean_closure_set(x_226, 3, x_225);
lean_inc(x_210);
x_227 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_226, x_210);
x_228 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_227, x_210);
x_229 = lean_alloc_closure((void*)(l_Lake_JobM_runFetchM), 9, 2);
lean_closure_set(x_229, 0, lean_box(0));
lean_closure_set(x_229, 1, x_228);
lean_inc(x_213);
x_230 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_230, 0, x_213);
x_231 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_231, 0, x_213);
if (lean_is_scalar(x_212)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_212;
}
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
x_233 = l_Lake_EquipT_instFunctor___redArg(x_232);
x_234 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_229, x_233);
return x_234;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonPUnit__lake___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Lake_instToJsonPUnit__lake() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instToJsonPUnit__lake___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonPUnit__lake___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instToJsonPUnit__lake___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
static uint32_t _init_l_Lake_noBuildCode() {
_start:
{
uint32_t x_1; 
x_1 = 3;
return x_1;
}
}
static uint64_t _init_l_Lake_platformTrace___closed__0() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = l_System_Platform_target;
x_2 = lean_string_hash(x_1);
return x_2;
}
}
static uint64_t _init_l_Lake_platformTrace___closed__1() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = l_Lake_platformTrace___closed__0;
x_2 = 1723;
x_3 = lean_uint64_mix_hash(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_platformTrace___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_platformTrace___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_platformTrace___closed__4() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lake_platformTrace___closed__3;
x_3 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_platformTrace___closed__5___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_Lake_platformTrace___closed__1;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_platformTrace___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_platformTrace___closed__4;
x_2 = l_Lake_platformTrace___closed__2;
x_3 = l_System_Platform_target;
x_4 = l_Lake_platformTrace___closed__5___boxed__const__1;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lake_platformTrace() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_platformTrace___closed__5;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lake_platformTrace;
x_6 = lean_box(0);
x_7 = l_Lake_BuildTrace_mix(x_4, x_5);
lean_ctor_set(x_1, 1, x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_10);
lean_dec(x_1);
x_13 = l_Lake_platformTrace;
x_14 = lean_box(0);
x_15 = l_Lake_BuildTrace_mix(x_12, x_13);
x_16 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_11);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_2);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Lake_platformTrace;
x_11 = lean_box(0);
x_12 = l_Lake_BuildTrace_mix(x_9, x_10);
lean_ctor_set(x_6, 1, x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_inc(x_15);
lean_dec(x_6);
x_18 = l_Lake_platformTrace;
x_19 = lean_box(0);
x_20 = l_Lake_BuildTrace_mix(x_17, x_18);
x_21 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*2, x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_7);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_addPlatformTrace(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = l_Lake_BuildTrace_mix(x_5, x_6);
lean_ctor_set(x_2, 1, x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_11);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = l_Lake_BuildTrace_mix(x_13, x_14);
x_17 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_12);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lake_addLeanTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_5, 2);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = l_Lake_BuildTrace_mix(x_9, x_10);
lean_ctor_set(x_6, 1, x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_inc(x_15);
lean_dec(x_6);
x_18 = lean_ctor_get(x_5, 2);
lean_inc(x_18);
lean_dec(x_5);
x_19 = lean_box(0);
x_20 = l_Lake_BuildTrace_mix(x_17, x_18);
x_21 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*2, x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_7);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_addLeanTrace(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Lake_addPureTrace___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_addPureTrace___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_3);
x_9 = lean_apply_1(x_2, x_3);
x_10 = lean_unbox_uint64(x_9);
lean_dec(x_9);
x_11 = l_Lake_addPureTrace___redArg___closed__0;
x_12 = lean_string_append(x_4, x_11);
x_13 = lean_apply_1(x_1, x_3);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = l_Lake_platformTrace___closed__2;
x_16 = l_Lake_platformTrace___closed__4;
x_17 = lean_box_uint64(x_10);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_16);
x_19 = lean_box(0);
x_20 = l_Lake_BuildTrace_mix(x_8, x_18);
lean_ctor_set(x_5, 1, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_5);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_6);
return x_22;
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; uint64_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get_uint8(x_5, sizeof(void*)*2);
x_25 = lean_ctor_get(x_5, 1);
lean_inc(x_25);
lean_inc(x_23);
lean_dec(x_5);
lean_inc(x_3);
x_26 = lean_apply_1(x_2, x_3);
x_27 = lean_unbox_uint64(x_26);
lean_dec(x_26);
x_28 = l_Lake_addPureTrace___redArg___closed__0;
x_29 = lean_string_append(x_4, x_28);
x_30 = lean_apply_1(x_1, x_3);
x_31 = lean_string_append(x_29, x_30);
lean_dec(x_30);
x_32 = l_Lake_platformTrace___closed__2;
x_33 = l_Lake_platformTrace___closed__4;
x_34 = lean_box_uint64(x_27);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_32);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set(x_35, 3, x_33);
x_36 = lean_box(0);
x_37 = l_Lake_BuildTrace_mix(x_25, x_35);
x_38 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_38, 0, x_23);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*2, x_24);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_6);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lake_addPureTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint64_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_4);
x_15 = lean_apply_1(x_3, x_4);
x_16 = lean_unbox_uint64(x_15);
lean_dec(x_15);
x_17 = l_Lake_addPureTrace___redArg___closed__0;
x_18 = lean_string_append(x_5, x_17);
x_19 = lean_apply_1(x_2, x_4);
x_20 = lean_string_append(x_18, x_19);
lean_dec(x_19);
x_21 = l_Lake_platformTrace___closed__2;
x_22 = l_Lake_platformTrace___closed__4;
x_23 = lean_box_uint64(x_16);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_23);
lean_ctor_set(x_24, 3, x_22);
x_25 = lean_box(0);
x_26 = l_Lake_BuildTrace_mix(x_14, x_24);
lean_ctor_set(x_11, 1, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_11);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_12);
return x_28;
}
else
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; uint64_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_29 = lean_ctor_get(x_11, 0);
x_30 = lean_ctor_get_uint8(x_11, sizeof(void*)*2);
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_inc(x_29);
lean_dec(x_11);
lean_inc(x_4);
x_32 = lean_apply_1(x_3, x_4);
x_33 = lean_unbox_uint64(x_32);
lean_dec(x_32);
x_34 = l_Lake_addPureTrace___redArg___closed__0;
x_35 = lean_string_append(x_5, x_34);
x_36 = lean_apply_1(x_2, x_4);
x_37 = lean_string_append(x_35, x_36);
lean_dec(x_36);
x_38 = l_Lake_platformTrace___closed__2;
x_39 = l_Lake_platformTrace___closed__4;
x_40 = lean_box_uint64(x_33);
x_41 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_38);
lean_ctor_set(x_41, 2, x_40);
lean_ctor_set(x_41, 3, x_39);
x_42 = lean_box(0);
x_43 = l_Lake_BuildTrace_mix(x_31, x_41);
x_44 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_44, 0, x_29);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*2, x_30);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_12);
return x_46;
}
}
}
LEAN_EXPORT lean_object* l_Lake_addPureTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_addPureTrace(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_13;
}
}
static lean_object* _init_l_Prod_toJson___at___Array_toJson___at_____private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178__spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Prod_toJson___at___Array_toJson___at_____private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178__spec__0_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_2);
x_5 = l_Prod_toJson___at___Array_toJson___at_____private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178__spec__0_spec__0___closed__0;
x_6 = lean_array_push(x_5, x_4);
x_7 = lean_array_push(x_6, x_3);
x_8 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_toJson___at_____private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178__spec__0_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Prod_toJson___at___Array_toJson___at_____private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178__spec__0_spec__0(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at_____private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178__spec__0(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l_Array_mapMUnsafe_map___at___Array_toJson___at_____private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178__spec__0_spec__1(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at_____private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178__spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_toJson___at_____private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178__spec__4_spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1411_(x_5);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at_____private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178__spec__4(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l_Array_mapMUnsafe_map___at___Array_toJson___at_____private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178__spec__4_spec__4(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata___closed__0____x40_Lake_Build_Common___hyg_178_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("depHash", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata___closed__1____x40_Lake_Build_Common___hyg_178_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inputs", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata___closed__2____x40_Lake_Build_Common___hyg_178_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("outputs", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata___closed__3____x40_Lake_Build_Common___hyg_178_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("log", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata___closed__4____x40_Lake_Build_Common___hyg_178_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata___closed__0____x40_Lake_Build_Common___hyg_178_;
x_7 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_8 = lean_uint64_to_nat(x_7);
x_9 = l_Lean_bignumToJson(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata___closed__1____x40_Lake_Build_Common___hyg_178_;
x_14 = l_Array_toJson___at_____private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178__spec__0(x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
x_17 = l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata___closed__2____x40_Lake_Build_Common___hyg_178_;
x_18 = l_Lean_Json_opt___at_____private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178__spec__3(x_17, x_4);
lean_dec(x_4);
x_19 = l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata___closed__3____x40_Lake_Build_Common___hyg_178_;
x_20 = l_Array_toJson___at_____private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178__spec__4(x_5);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_11);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_26);
x_28 = l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata___closed__4____x40_Lake_Build_Common___hyg_178_;
x_29 = l_List_flatMapTR_go___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonPosition____x40_Lean_Data_Lsp_Basic___hyg_226__spec__0(x_27, x_28);
x_30 = l_Lean_Json_mkObj(x_29);
return x_30;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_toJson___at_____private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178__spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Array_toJson___at_____private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178__spec__0_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at_____private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178__spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_opt___at_____private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178__spec__3(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_toJson___at_____private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178__spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Array_toJson___at_____private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178__spec__4_spec__4(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lake_instToJsonBuildMetadata___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instToJsonBuildMetadata() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instToJsonBuildMetadata___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofHash(uint64_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata___closed__4____x40_Lake_Build_Common___hyg_178_;
x_3 = lean_box(0);
x_4 = lean_box_uint64(x_1);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofHash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lake_BuildMetadata_ofHash(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0_spec__0_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = l___private_Lake_Util_Log_0__Lake_fromJsonLogEntry____x40_Lake_Util_Log___hyg_1463_(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_3);
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
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_box(0);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_13, x_2, x_11);
x_2 = x_15;
x_3 = x_16;
goto _start;
}
}
}
}
static lean_object* _init_l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_array_size(x_2);
x_4 = 0;
x_5 = l_Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0_spec__0_spec__0(x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0_spec__0___closed__0;
x_7 = lean_unsigned_to_nat(80u);
x_8 = l_Lean_Json_pretty(x_1, x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec(x_8);
x_10 = l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0_spec__0___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
static lean_object* _init_l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0___closed__0;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0_spec__0(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
}
static lean_object* _init_l_Option_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__3_spec__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__3_spec__3(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__3_spec__3___closed__0;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
}
static lean_object* _init_l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__3(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__3___closed__0;
return x_2;
}
else
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Option_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__3_spec__3(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
}
static lean_object* _init_l_Prod_fromJson_x3f___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5_spec__5_spec__5___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected pair, got '", 20, 20);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5_spec__5_spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_dec(x_11);
x_2 = x_1;
goto block_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_fget(x_11, x_15);
x_17 = l_Lean_Json_getStr_x3f(x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_11);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_array_fget(x_11, x_23);
lean_dec(x_11);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_17, 0, x_25);
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_array_fget(x_11, x_27);
lean_dec(x_11);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
}
else
{
x_2 = x_1;
goto block_10;
}
block_10:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l_Prod_fromJson_x3f___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5_spec__5_spec__5___closed__0;
x_4 = lean_unsigned_to_nat(80u);
x_5 = l_Lean_Json_pretty(x_2, x_4);
x_6 = lean_string_append(x_3, x_5);
lean_dec(x_5);
x_7 = l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0_spec__0___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5_spec__5_spec__6(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = l_Prod_fromJson_x3f___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5_spec__5_spec__5(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_3);
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
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_box(0);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_13, x_2, x_11);
x_2 = x_15;
x_3 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5_spec__5(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_array_size(x_2);
x_4 = 0;
x_5 = l_Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5_spec__5_spec__6(x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0_spec__0___closed__0;
x_7 = lean_unsigned_to_nat(80u);
x_8 = l_Lean_Json_pretty(x_1, x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec(x_8);
x_10 = l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0_spec__0___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
static lean_object* _init_l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5___closed__0;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5_spec__5(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("property not found: depHash", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_BuildMetadata_fromJson_x3f___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("depHash: ", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("log: ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("outputs: ", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inputs: ", 8, 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJson_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_getObj_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata___closed__0____x40_Lake_Build_Common___hyg_178_;
x_8 = l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec(x_6);
x_9 = l_Lake_BuildMetadata_fromJson_x3f___closed__1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_UInt64_fromJson_x3f(x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_6);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l_Lake_BuildMetadata_fromJson_x3f___closed__2;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = l_Lake_BuildMetadata_fromJson_x3f___closed__2;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_28; lean_object* x_29; lean_object* x_32; lean_object* x_33; lean_object* x_52; lean_object* x_55; lean_object* x_65; lean_object* x_66; 
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_21 = x_11;
} else {
 lean_dec_ref(x_11);
 x_21 = lean_box(0);
}
x_65 = l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata___closed__1____x40_Lake_Build_Common___hyg_178_;
x_66 = l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(x_6, x_65);
if (lean_obj_tag(x_66) == 0)
{
goto block_64;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec(x_66);
x_68 = l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5(x_67);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_6);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_68, 0);
x_71 = l_Lake_BuildMetadata_fromJson_x3f___closed__7;
x_72 = lean_string_append(x_71, x_70);
lean_dec(x_70);
lean_ctor_set(x_68, 0, x_72);
return x_68;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_68, 0);
lean_inc(x_73);
lean_dec(x_68);
x_74 = l_Lake_BuildMetadata_fromJson_x3f___closed__7;
x_75 = lean_string_append(x_74, x_73);
lean_dec(x_73);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
else
{
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_77; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_6);
x_77 = !lean_is_exclusive(x_68);
if (x_77 == 0)
{
lean_ctor_set_tag(x_68, 0);
return x_68;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_68, 0);
lean_inc(x_78);
lean_dec(x_68);
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
}
else
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_68, 0);
lean_inc(x_80);
lean_dec(x_68);
if (lean_obj_tag(x_80) == 0)
{
goto block_64;
}
else
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec(x_80);
x_55 = x_81;
goto block_62;
}
}
}
}
block_27:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_23);
lean_ctor_set(x_25, 3, x_24);
if (lean_is_scalar(x_21)) {
 x_26 = lean_alloc_ctor(1, 1, 0);
} else {
 x_26 = x_21;
}
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
block_31:
{
lean_object* x_30; 
x_30 = l_Lake_BuildMetadata_fromJson_x3f___closed__3;
x_22 = x_28;
x_23 = x_29;
x_24 = x_30;
goto block_27;
}
block_51:
{
lean_object* x_34; lean_object* x_35; 
x_34 = l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata___closed__3____x40_Lake_Build_Common___hyg_178_;
x_35 = l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(x_6, x_34);
lean_dec(x_6);
if (lean_obj_tag(x_35) == 0)
{
x_28 = x_32;
x_29 = x_33;
goto block_31;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0(x_36);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_21);
lean_dec(x_20);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = l_Lake_BuildMetadata_fromJson_x3f___closed__4;
x_41 = lean_string_append(x_40, x_39);
lean_dec(x_39);
lean_ctor_set(x_37, 0, x_41);
return x_37;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_37, 0);
lean_inc(x_42);
lean_dec(x_37);
x_43 = l_Lake_BuildMetadata_fromJson_x3f___closed__4;
x_44 = lean_string_append(x_43, x_42);
lean_dec(x_42);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
else
{
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_46; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_21);
lean_dec(x_20);
x_46 = !lean_is_exclusive(x_37);
if (x_46 == 0)
{
lean_ctor_set_tag(x_37, 0);
return x_37;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_37, 0);
lean_inc(x_47);
lean_dec(x_37);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
else
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_37, 0);
lean_inc(x_49);
lean_dec(x_37);
if (lean_obj_tag(x_49) == 0)
{
x_28 = x_32;
x_29 = x_33;
goto block_31;
}
else
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec(x_49);
x_22 = x_32;
x_23 = x_33;
x_24 = x_50;
goto block_27;
}
}
}
}
}
block_54:
{
lean_object* x_53; 
x_53 = lean_box(0);
x_32 = x_52;
x_33 = x_53;
goto block_51;
}
block_62:
{
lean_object* x_56; lean_object* x_57; 
x_56 = l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata___closed__2____x40_Lake_Build_Common___hyg_178_;
x_57 = l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(x_6, x_56);
if (lean_obj_tag(x_57) == 0)
{
x_52 = x_55;
goto block_54;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec(x_57);
x_59 = l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__3(x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec(x_59);
if (lean_obj_tag(x_60) == 0)
{
x_52 = x_55;
goto block_54;
}
else
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec(x_60);
x_32 = x_55;
x_33 = x_61;
goto block_51;
}
}
}
block_64:
{
lean_object* x_63; 
x_63 = l_Lake_BuildMetadata_fromJson_x3f___closed__6;
x_55 = x_63;
goto block_62;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0_spec__0_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5_spec__5_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5_spec__5_spec__6(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lake_instFromJsonBuildMetadata___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_BuildMetadata_fromJson_x3f), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instFromJsonBuildMetadata() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instFromJsonBuildMetadata___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_readTraceFile___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": invalid trace file: ", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lake_readTraceFile___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": read failed: ", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_readTraceFile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_readFile(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_7 = x_4;
} else {
 lean_dec_ref(x_4);
 x_7 = lean_box(0);
}
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_string_utf8_byte_size(x_5);
x_22 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_5, x_21, x_20);
x_23 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_5, x_22, x_21);
x_24 = lean_string_utf8_extract(x_5, x_22, x_23);
lean_dec(x_23);
lean_dec(x_22);
x_25 = l_Lake_Hash_ofString_x3f(x_24);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = l_Lean_Json_parse(x_5);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_8 = x_27;
goto block_19;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lake_BuildMetadata_fromJson_x3f(x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_8 = x_30;
goto block_19;
}
else
{
uint8_t x_31; 
lean_dec(x_7);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_ctor_set_tag(x_29, 2);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_2);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_6);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_2);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_6);
return x_37;
}
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_25);
if (x_38 == 0)
{
lean_object* x_39; uint64_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_25, 0);
x_40 = lean_unbox_uint64(x_39);
lean_dec(x_39);
x_41 = l_Lake_BuildMetadata_ofHash(x_40);
lean_ctor_set_tag(x_25, 2);
lean_ctor_set(x_25, 0, x_41);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_25);
lean_ctor_set(x_42, 1, x_2);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_6);
return x_43;
}
else
{
lean_object* x_44; uint64_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_25, 0);
lean_inc(x_44);
lean_dec(x_25);
x_45 = lean_unbox_uint64(x_44);
lean_dec(x_44);
x_46 = l_Lake_BuildMetadata_ofHash(x_45);
x_47 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_2);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_6);
return x_49;
}
}
block_19:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = l_Lake_readTraceFile___closed__0;
x_10 = lean_string_append(x_1, x_9);
x_11 = lean_string_append(x_10, x_8);
lean_dec(x_8);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_11);
x_14 = lean_unbox(x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_14);
x_15 = lean_array_push(x_2, x_13);
x_16 = lean_box(1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
if (lean_is_scalar(x_7)) {
 x_18 = lean_alloc_ctor(0, 2, 0);
} else {
 x_18 = x_7;
}
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_6);
return x_18;
}
}
else
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_4, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 11)
{
uint8_t x_51; 
lean_dec(x_50);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_4);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_4, 0);
lean_dec(x_52);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_2);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_54);
return x_4;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_4, 1);
lean_inc(x_55);
lean_dec(x_4);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_2);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_4);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_60 = lean_ctor_get(x_4, 0);
lean_dec(x_60);
x_61 = l_Lake_readTraceFile___closed__1;
x_62 = lean_string_append(x_1, x_61);
x_63 = lean_io_error_to_string(x_50);
x_64 = lean_string_append(x_62, x_63);
lean_dec(x_63);
x_65 = lean_box(2);
x_66 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_66, 0, x_64);
x_67 = lean_unbox(x_65);
lean_ctor_set_uint8(x_66, sizeof(void*)*1, x_67);
x_68 = lean_array_push(x_2, x_66);
x_69 = lean_box(1);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_70);
return x_4;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_71 = lean_ctor_get(x_4, 1);
lean_inc(x_71);
lean_dec(x_4);
x_72 = l_Lake_readTraceFile___closed__1;
x_73 = lean_string_append(x_1, x_72);
x_74 = lean_io_error_to_string(x_50);
x_75 = lean_string_append(x_73, x_74);
lean_dec(x_74);
x_76 = lean_box(2);
x_77 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_77, 0, x_75);
x_78 = lean_unbox(x_76);
lean_ctor_set_uint8(x_77, sizeof(void*)*1, x_78);
x_79 = lean_array_push(x_2, x_77);
x_80 = lean_box(1);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_71);
return x_82;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_readTraceFile_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lake_readTraceFile(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 2)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_5, 0);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_ctor_set_tag(x_6, 1);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_5, 0, x_13);
return x_4;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_16 = x_6;
} else {
 lean_dec_ref(x_6);
 x_16 = lean_box(0);
}
if (lean_is_scalar(x_16)) {
 x_17 = lean_alloc_ctor(1, 1, 0);
} else {
 x_17 = x_16;
 lean_ctor_set_tag(x_17, 1);
}
lean_ctor_set(x_17, 0, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_4, 0, x_18);
return x_4;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_dec(x_4);
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_21 = x_5;
} else {
 lean_dec_ref(x_5);
 x_21 = lean_box(0);
}
x_22 = lean_ctor_get(x_6, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_23 = x_6;
} else {
 lean_dec_ref(x_6);
 x_23 = lean_box(0);
}
if (lean_is_scalar(x_23)) {
 x_24 = lean_alloc_ctor(1, 1, 0);
} else {
 x_24 = x_23;
 lean_ctor_set_tag(x_24, 1);
}
lean_ctor_set(x_24, 0, x_22);
if (lean_is_scalar(x_21)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_21;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_19);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_6);
x_27 = !lean_is_exclusive(x_4);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_4, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_5);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_5, 1);
x_31 = lean_ctor_get(x_5, 0);
lean_dec(x_31);
x_32 = lean_array_get_size(x_30);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_32);
return x_4;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_5, 1);
lean_inc(x_33);
lean_dec(x_5);
x_34 = lean_array_get_size(x_33);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_4, 0, x_35);
return x_4;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_4, 1);
lean_inc(x_36);
lean_dec(x_4);
x_37 = lean_ctor_get(x_5, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_38 = x_5;
} else {
 lean_dec_ref(x_5);
 x_38 = lean_box(0);
}
x_39 = lean_array_get_size(x_37);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_38;
 lean_ctor_set_tag(x_40, 1);
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_36);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_serializeInputs_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_6 = lean_array_uget(x_1, x_2);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 2);
lean_inc(x_16);
x_17 = l_Array_isEmpty___redArg(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_16);
x_18 = l___private_Lake_Build_Common_0__Lake_serializeInputs(x_15);
lean_dec(x_15);
x_19 = l_Array_toJson___at_____private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178__spec__0(x_18);
x_7 = x_19;
goto block_14;
}
else
{
uint64_t x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_15);
x_20 = lean_unbox_uint64(x_16);
lean_dec(x_16);
x_21 = lean_uint64_to_nat(x_20);
x_22 = l_Lean_bignumToJson(x_21);
x_7 = x_22;
goto block_14;
}
block_14:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_array_push(x_4, x_9);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_10;
goto _start;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_6 = lean_array_uget(x_1, x_2);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 2);
lean_inc(x_16);
x_17 = l_Array_isEmpty___redArg(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_16);
x_18 = l___private_Lake_Build_Common_0__Lake_serializeInputs(x_15);
lean_dec(x_15);
x_19 = l_Array_toJson___at_____private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178__spec__0(x_18);
x_7 = x_19;
goto block_14;
}
else
{
uint64_t x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_15);
x_20 = lean_unbox_uint64(x_16);
lean_dec(x_16);
x_21 = lean_uint64_to_nat(x_20);
x_22 = l_Lean_bignumToJson(x_21);
x_7 = x_22;
goto block_14;
}
block_14:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_array_push(x_4, x_9);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_13 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_serializeInputs_spec__0_spec__0(x_1, x_12, x_3, x_10);
return x_13;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_serializeInputs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = l_Lake_BuildMetadata_fromJson_x3f___closed__6;
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(x_1, x_7, x_8, x_2);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_serializeInputs_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_serializeInputs_spec__0_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_serializeInputs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_serializeInputs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Build_Common_0__Lake_serializeInputs(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_writeTraceFile_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_createParentDirs(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_2, 3);
lean_dec(x_11);
x_12 = lean_ctor_get(x_2, 0);
lean_dec(x_12);
x_13 = l___private_Lake_Build_Common_0__Lake_serializeInputs(x_9);
lean_dec(x_9);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_2, 3, x_4);
lean_ctor_set(x_2, 2, x_14);
lean_ctor_set(x_2, 1, x_13);
lean_ctor_set(x_2, 0, x_10);
x_15 = l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178_(x_2);
x_16 = lean_unsigned_to_nat(80u);
x_17 = l_Lean_Json_pretty(x_15, x_16);
x_18 = l_IO_FS_writeFile(x_1, x_17, x_7);
lean_dec(x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_2, 1);
x_20 = lean_ctor_get(x_2, 2);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_2);
x_21 = l___private_Lake_Build_Common_0__Lake_serializeInputs(x_19);
lean_dec(x_19);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_3);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_22);
lean_ctor_set(x_23, 3, x_4);
x_24 = l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178_(x_23);
x_25 = lean_unsigned_to_nat(80u);
x_26 = l_Lean_Json_pretty(x_24, x_25);
x_27 = l_IO_FS_writeFile(x_1, x_26, x_7);
lean_dec(x_26);
return x_27;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lake_writeTraceFile_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_writeTraceFile_go(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_writeTraceFile___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_apply_1(x_1, x_4);
x_8 = l_Lake_writeTraceFile_go(x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_writeTraceFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_apply_1(x_2, x_5);
x_9 = l_Lake_writeTraceFile_go(x_3, x_4, x_8, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_writeTraceFile___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_writeTraceFile___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_writeTraceFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_writeTraceFile(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
static lean_object* _init_l_Lake_checkHashUpToDate___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_beqHash____x40_Lake_Build_Trace___hyg_486____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_4, 2);
x_11 = l_Lake_checkHashUpToDate___redArg___closed__0;
lean_inc(x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_10);
x_13 = l_Option_beqOption___redArg____x40_Init_Data_Option_Basic___hyg_160_(x_11, x_12, x_5);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_8);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lake_MTime_checkUpToDate___redArg(x_2, x_3, x_6, x_9);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_8);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_8);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
else
{
lean_object* x_27; uint8_t x_28; 
lean_dec(x_2);
x_27 = lean_apply_2(x_1, x_3, x_9);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_8);
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
lean_ctor_set(x_33, 1, x_8);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lake_checkHashUpToDate___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_checkHashUpToDate___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lake_checkHashUpToDate(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_box(0);
x_13 = lean_array_push(x_11, x_2);
lean_ctor_set(x_8, 0, x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_16);
lean_dec(x_8);
x_19 = lean_box(0);
x_20 = lean_array_push(x_16, x_2);
x_21 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
lean_ctor_set_uint8(x_21, sizeof(void*)*2, x_17);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_9);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_28; uint8_t x_29; 
x_28 = l_Lake_instMonadWorkspaceJobM___closed__0;
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_32 = lean_ctor_get(x_28, 1);
x_33 = lean_ctor_get(x_30, 0);
x_34 = lean_ctor_get(x_30, 1);
x_35 = lean_ctor_get(x_30, 4);
lean_dec(x_35);
x_36 = lean_ctor_get(x_30, 3);
lean_dec(x_36);
x_37 = lean_ctor_get(x_30, 2);
lean_dec(x_37);
lean_inc(x_32);
lean_inc(x_34);
x_38 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_38, 0, x_34);
lean_closure_set(x_38, 1, x_32);
lean_inc(x_32);
lean_inc(x_34);
x_39 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_39, 0, x_34);
lean_closure_set(x_39, 1, x_32);
lean_inc(x_38);
lean_inc(x_34);
x_40 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_40, 0, x_34);
lean_closure_set(x_40, 1, x_38);
lean_inc(x_34);
lean_inc(x_33);
x_41 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_41, 0, x_33);
lean_closure_set(x_41, 1, x_34);
lean_closure_set(x_41, 2, x_32);
x_42 = l_Lake_EStateT_instFunctor___redArg(x_33);
x_43 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_43, 0, x_34);
lean_ctor_set(x_30, 4, x_39);
lean_ctor_set(x_30, 3, x_40);
lean_ctor_set(x_30, 2, x_41);
lean_ctor_set(x_30, 1, x_43);
lean_ctor_set(x_30, 0, x_42);
lean_ctor_set(x_28, 1, x_38);
x_44 = l_ReaderT_instMonad___redArg(x_28);
x_45 = l_ReaderT_instMonad___redArg(x_44);
x_46 = l_ReaderT_instMonad___redArg(x_45);
x_47 = l_ReaderT_instMonad___redArg(x_46);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_47);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_48 = lean_ctor_get(x_4, 3);
x_49 = l_Lake_MTime_checkUpToDate___redArg(x_2, x_3, x_48, x_13);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_12);
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
lean_ctor_set(x_55, 1, x_12);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
case 1:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_66; uint8_t x_67; 
lean_dec(x_47);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_57 = l_Lake_MTime_checkUpToDate___redArg(x_2, x_3, x_6, x_13);
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
x_66 = lean_ctor_get(x_11, 0);
lean_inc(x_66);
lean_dec(x_11);
x_67 = lean_ctor_get_uint8(x_66, sizeof(void*)*1);
lean_dec(x_66);
if (x_67 == 0)
{
lean_dec(x_58);
x_61 = x_67;
goto block_65;
}
else
{
uint8_t x_68; 
x_68 = lean_unbox(x_58);
lean_dec(x_58);
x_61 = x_68;
goto block_65;
}
block_65:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_box(x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_12);
if (lean_is_scalar(x_60)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_60;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_59);
return x_64;
}
}
default: 
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_5);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_70 = lean_ctor_get(x_5, 0);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 3);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_4, 2);
x_74 = lean_alloc_closure((void*)(l_Lake_SavedTrace_replayIfUpToDate___redArg___lam__0___boxed), 9, 0);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_71);
x_136 = l_Lake_checkHashUpToDate___redArg___closed__0;
lean_inc(x_73);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_73);
x_138 = l_Option_beqOption___redArg____x40_Init_Data_Option_Basic___hyg_160_(x_136, x_137, x_5);
if (x_138 == 0)
{
lean_object* x_139; uint8_t x_140; 
lean_dec(x_1);
x_139 = lean_ctor_get(x_11, 0);
lean_inc(x_139);
x_140 = lean_ctor_get_uint8(x_139, sizeof(void*)*1);
lean_dec(x_139);
if (x_140 == 0)
{
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_47);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_14 = x_140;
x_15 = x_12;
x_16 = x_13;
goto block_20;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_141 = l_Lake_MTime_checkUpToDate___redArg(x_2, x_3, x_6, x_13);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_unbox(x_142);
lean_dec(x_142);
x_75 = x_144;
x_76 = x_12;
x_77 = x_143;
goto block_135;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
lean_dec(x_2);
x_145 = lean_apply_2(x_1, x_3, x_13);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_unbox(x_146);
lean_dec(x_146);
x_75 = x_148;
x_76 = x_12;
x_77 = x_147;
goto block_135;
}
block_135:
{
if (x_75 == 0)
{
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_47);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_14 = x_75;
x_15 = x_76;
x_16 = x_77;
goto block_20;
}
else
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_76);
if (x_78 == 0)
{
uint8_t x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_79 = lean_ctor_get_uint8(x_76, sizeof(void*)*2);
x_80 = l_Lake_EquipT_instMonad___redArg(x_47);
x_81 = lean_box(1);
x_82 = lean_unbox(x_81);
x_83 = l_Lake_JobAction_merge(x_79, x_82);
lean_ctor_set_uint8(x_76, sizeof(void*)*2, x_83);
x_84 = lean_unsigned_to_nat(0u);
x_85 = lean_array_get_size(x_72);
x_86 = lean_nat_dec_lt(x_84, x_85);
if (x_86 == 0)
{
lean_dec(x_85);
lean_dec(x_80);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_21 = x_75;
x_22 = x_76;
x_23 = x_77;
goto block_27;
}
else
{
uint8_t x_87; 
x_87 = lean_nat_dec_le(x_85, x_85);
if (x_87 == 0)
{
lean_dec(x_85);
lean_dec(x_80);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_21 = x_75;
x_22 = x_76;
x_23 = x_77;
goto block_27;
}
else
{
lean_object* x_88; size_t x_89; size_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_88 = lean_box(0);
x_89 = 0;
x_90 = lean_usize_of_nat(x_85);
lean_dec(x_85);
x_91 = l_Array_foldlMUnsafe_fold___redArg(x_80, x_74, x_72, x_89, x_90, x_88);
x_92 = lean_apply_7(x_91, x_7, x_8, x_9, x_10, x_11, x_76, x_77);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_21 = x_75;
x_22 = x_95;
x_23 = x_94;
goto block_27;
}
else
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_92);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_92, 0);
lean_dec(x_97);
x_98 = !lean_is_exclusive(x_93);
if (x_98 == 0)
{
return x_92;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_93, 0);
x_100 = lean_ctor_get(x_93, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_93);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set(x_92, 0, x_101);
return x_92;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_102 = lean_ctor_get(x_92, 1);
lean_inc(x_102);
lean_dec(x_92);
x_103 = lean_ctor_get(x_93, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_93, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_105 = x_93;
} else {
 lean_dec_ref(x_93);
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
}
}
else
{
lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_108 = lean_ctor_get(x_76, 0);
x_109 = lean_ctor_get_uint8(x_76, sizeof(void*)*2);
x_110 = lean_ctor_get(x_76, 1);
lean_inc(x_110);
lean_inc(x_108);
lean_dec(x_76);
x_111 = l_Lake_EquipT_instMonad___redArg(x_47);
x_112 = lean_box(1);
x_113 = lean_unbox(x_112);
x_114 = l_Lake_JobAction_merge(x_109, x_113);
x_115 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_115, 0, x_108);
lean_ctor_set(x_115, 1, x_110);
lean_ctor_set_uint8(x_115, sizeof(void*)*2, x_114);
x_116 = lean_unsigned_to_nat(0u);
x_117 = lean_array_get_size(x_72);
x_118 = lean_nat_dec_lt(x_116, x_117);
if (x_118 == 0)
{
lean_dec(x_117);
lean_dec(x_111);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_21 = x_75;
x_22 = x_115;
x_23 = x_77;
goto block_27;
}
else
{
uint8_t x_119; 
x_119 = lean_nat_dec_le(x_117, x_117);
if (x_119 == 0)
{
lean_dec(x_117);
lean_dec(x_111);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_21 = x_75;
x_22 = x_115;
x_23 = x_77;
goto block_27;
}
else
{
lean_object* x_120; size_t x_121; size_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_120 = lean_box(0);
x_121 = 0;
x_122 = lean_usize_of_nat(x_117);
lean_dec(x_117);
x_123 = l_Array_foldlMUnsafe_fold___redArg(x_111, x_74, x_72, x_121, x_122, x_120);
x_124 = lean_apply_7(x_123, x_7, x_8, x_9, x_10, x_11, x_115, x_77);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_21 = x_75;
x_22 = x_127;
x_23 = x_126;
goto block_27;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_128 = lean_ctor_get(x_124, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_129 = x_124;
} else {
 lean_dec_ref(x_124);
 x_129 = lean_box(0);
}
x_130 = lean_ctor_get(x_125, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_125, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_132 = x_125;
} else {
 lean_dec_ref(x_125);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(1, 2, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_131);
if (lean_is_scalar(x_129)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_129;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_128);
return x_134;
}
}
}
}
}
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_149 = lean_ctor_get(x_5, 0);
lean_inc(x_149);
lean_dec(x_5);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 3);
lean_inc(x_151);
lean_dec(x_149);
x_152 = lean_ctor_get(x_4, 2);
x_153 = lean_alloc_closure((void*)(l_Lake_SavedTrace_replayIfUpToDate___redArg___lam__0___boxed), 9, 0);
x_186 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_186, 0, x_150);
x_187 = l_Lake_checkHashUpToDate___redArg___closed__0;
lean_inc(x_152);
x_188 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_188, 0, x_152);
x_189 = l_Option_beqOption___redArg____x40_Init_Data_Option_Basic___hyg_160_(x_187, x_188, x_186);
if (x_189 == 0)
{
lean_object* x_190; uint8_t x_191; 
lean_dec(x_1);
x_190 = lean_ctor_get(x_11, 0);
lean_inc(x_190);
x_191 = lean_ctor_get_uint8(x_190, sizeof(void*)*1);
lean_dec(x_190);
if (x_191 == 0)
{
lean_dec(x_153);
lean_dec(x_151);
lean_dec(x_47);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_14 = x_191;
x_15 = x_12;
x_16 = x_13;
goto block_20;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_192 = l_Lake_MTime_checkUpToDate___redArg(x_2, x_3, x_6, x_13);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = lean_unbox(x_193);
lean_dec(x_193);
x_154 = x_195;
x_155 = x_12;
x_156 = x_194;
goto block_185;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
lean_dec(x_2);
x_196 = lean_apply_2(x_1, x_3, x_13);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_199 = lean_unbox(x_197);
lean_dec(x_197);
x_154 = x_199;
x_155 = x_12;
x_156 = x_198;
goto block_185;
}
block_185:
{
if (x_154 == 0)
{
lean_dec(x_153);
lean_dec(x_151);
lean_dec(x_47);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_14 = x_154;
x_15 = x_155;
x_16 = x_156;
goto block_20;
}
else
{
lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; uint8_t x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_157 = lean_ctor_get(x_155, 0);
lean_inc(x_157);
x_158 = lean_ctor_get_uint8(x_155, sizeof(void*)*2);
x_159 = lean_ctor_get(x_155, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_160 = x_155;
} else {
 lean_dec_ref(x_155);
 x_160 = lean_box(0);
}
x_161 = l_Lake_EquipT_instMonad___redArg(x_47);
x_162 = lean_box(1);
x_163 = lean_unbox(x_162);
x_164 = l_Lake_JobAction_merge(x_158, x_163);
if (lean_is_scalar(x_160)) {
 x_165 = lean_alloc_ctor(0, 2, 1);
} else {
 x_165 = x_160;
}
lean_ctor_set(x_165, 0, x_157);
lean_ctor_set(x_165, 1, x_159);
lean_ctor_set_uint8(x_165, sizeof(void*)*2, x_164);
x_166 = lean_unsigned_to_nat(0u);
x_167 = lean_array_get_size(x_151);
x_168 = lean_nat_dec_lt(x_166, x_167);
if (x_168 == 0)
{
lean_dec(x_167);
lean_dec(x_161);
lean_dec(x_153);
lean_dec(x_151);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_21 = x_154;
x_22 = x_165;
x_23 = x_156;
goto block_27;
}
else
{
uint8_t x_169; 
x_169 = lean_nat_dec_le(x_167, x_167);
if (x_169 == 0)
{
lean_dec(x_167);
lean_dec(x_161);
lean_dec(x_153);
lean_dec(x_151);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_21 = x_154;
x_22 = x_165;
x_23 = x_156;
goto block_27;
}
else
{
lean_object* x_170; size_t x_171; size_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_170 = lean_box(0);
x_171 = 0;
x_172 = lean_usize_of_nat(x_167);
lean_dec(x_167);
x_173 = l_Array_foldlMUnsafe_fold___redArg(x_161, x_153, x_151, x_171, x_172, x_170);
x_174 = lean_apply_7(x_173, x_7, x_8, x_9, x_10, x_11, x_165, x_156);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec(x_174);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_21 = x_154;
x_22 = x_177;
x_23 = x_176;
goto block_27;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_178 = lean_ctor_get(x_174, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_179 = x_174;
} else {
 lean_dec_ref(x_174);
 x_179 = lean_box(0);
}
x_180 = lean_ctor_get(x_175, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_175, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_182 = x_175;
} else {
 lean_dec_ref(x_175);
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
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_200 = lean_ctor_get(x_28, 1);
x_201 = lean_ctor_get(x_30, 0);
x_202 = lean_ctor_get(x_30, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_30);
lean_inc(x_200);
lean_inc(x_202);
x_203 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_203, 0, x_202);
lean_closure_set(x_203, 1, x_200);
lean_inc(x_200);
lean_inc(x_202);
x_204 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_204, 0, x_202);
lean_closure_set(x_204, 1, x_200);
lean_inc(x_203);
lean_inc(x_202);
x_205 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_205, 0, x_202);
lean_closure_set(x_205, 1, x_203);
lean_inc(x_202);
lean_inc(x_201);
x_206 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_206, 0, x_201);
lean_closure_set(x_206, 1, x_202);
lean_closure_set(x_206, 2, x_200);
x_207 = l_Lake_EStateT_instFunctor___redArg(x_201);
x_208 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_208, 0, x_202);
x_209 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
lean_ctor_set(x_209, 2, x_206);
lean_ctor_set(x_209, 3, x_205);
lean_ctor_set(x_209, 4, x_204);
lean_ctor_set(x_28, 1, x_203);
lean_ctor_set(x_28, 0, x_209);
x_210 = l_ReaderT_instMonad___redArg(x_28);
x_211 = l_ReaderT_instMonad___redArg(x_210);
x_212 = l_ReaderT_instMonad___redArg(x_211);
x_213 = l_ReaderT_instMonad___redArg(x_212);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_213);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_214 = lean_ctor_get(x_4, 3);
x_215 = l_Lake_MTime_checkUpToDate___redArg(x_2, x_3, x_214, x_13);
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_218 = x_215;
} else {
 lean_dec_ref(x_215);
 x_218 = lean_box(0);
}
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_216);
lean_ctor_set(x_219, 1, x_12);
if (lean_is_scalar(x_218)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_218;
}
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_217);
return x_220;
}
case 1:
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; lean_object* x_230; uint8_t x_231; 
lean_dec(x_213);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_221 = l_Lake_MTime_checkUpToDate___redArg(x_2, x_3, x_6, x_13);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_224 = x_221;
} else {
 lean_dec_ref(x_221);
 x_224 = lean_box(0);
}
x_230 = lean_ctor_get(x_11, 0);
lean_inc(x_230);
lean_dec(x_11);
x_231 = lean_ctor_get_uint8(x_230, sizeof(void*)*1);
lean_dec(x_230);
if (x_231 == 0)
{
lean_dec(x_222);
x_225 = x_231;
goto block_229;
}
else
{
uint8_t x_232; 
x_232 = lean_unbox(x_222);
lean_dec(x_222);
x_225 = x_232;
goto block_229;
}
block_229:
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_box(x_225);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_12);
if (lean_is_scalar(x_224)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_224;
}
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_223);
return x_228;
}
}
default: 
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; lean_object* x_240; lean_object* x_241; lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; 
x_233 = lean_ctor_get(x_5, 0);
lean_inc(x_233);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_234 = x_5;
} else {
 lean_dec_ref(x_5);
 x_234 = lean_box(0);
}
x_235 = lean_ctor_get(x_233, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_233, 3);
lean_inc(x_236);
lean_dec(x_233);
x_237 = lean_ctor_get(x_4, 2);
x_238 = lean_alloc_closure((void*)(l_Lake_SavedTrace_replayIfUpToDate___redArg___lam__0___boxed), 9, 0);
if (lean_is_scalar(x_234)) {
 x_271 = lean_alloc_ctor(1, 1, 0);
} else {
 x_271 = x_234;
 lean_ctor_set_tag(x_271, 1);
}
lean_ctor_set(x_271, 0, x_235);
x_272 = l_Lake_checkHashUpToDate___redArg___closed__0;
lean_inc(x_237);
x_273 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_273, 0, x_237);
x_274 = l_Option_beqOption___redArg____x40_Init_Data_Option_Basic___hyg_160_(x_272, x_273, x_271);
if (x_274 == 0)
{
lean_object* x_275; uint8_t x_276; 
lean_dec(x_1);
x_275 = lean_ctor_get(x_11, 0);
lean_inc(x_275);
x_276 = lean_ctor_get_uint8(x_275, sizeof(void*)*1);
lean_dec(x_275);
if (x_276 == 0)
{
lean_dec(x_238);
lean_dec(x_236);
lean_dec(x_213);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_14 = x_276;
x_15 = x_12;
x_16 = x_13;
goto block_20;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; 
x_277 = l_Lake_MTime_checkUpToDate___redArg(x_2, x_3, x_6, x_13);
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
lean_dec(x_277);
x_280 = lean_unbox(x_278);
lean_dec(x_278);
x_239 = x_280;
x_240 = x_12;
x_241 = x_279;
goto block_270;
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; 
lean_dec(x_2);
x_281 = lean_apply_2(x_1, x_3, x_13);
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec(x_281);
x_284 = lean_unbox(x_282);
lean_dec(x_282);
x_239 = x_284;
x_240 = x_12;
x_241 = x_283;
goto block_270;
}
block_270:
{
if (x_239 == 0)
{
lean_dec(x_238);
lean_dec(x_236);
lean_dec(x_213);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_14 = x_239;
x_15 = x_240;
x_16 = x_241;
goto block_20;
}
else
{
lean_object* x_242; uint8_t x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; uint8_t x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; 
x_242 = lean_ctor_get(x_240, 0);
lean_inc(x_242);
x_243 = lean_ctor_get_uint8(x_240, sizeof(void*)*2);
x_244 = lean_ctor_get(x_240, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_245 = x_240;
} else {
 lean_dec_ref(x_240);
 x_245 = lean_box(0);
}
x_246 = l_Lake_EquipT_instMonad___redArg(x_213);
x_247 = lean_box(1);
x_248 = lean_unbox(x_247);
x_249 = l_Lake_JobAction_merge(x_243, x_248);
if (lean_is_scalar(x_245)) {
 x_250 = lean_alloc_ctor(0, 2, 1);
} else {
 x_250 = x_245;
}
lean_ctor_set(x_250, 0, x_242);
lean_ctor_set(x_250, 1, x_244);
lean_ctor_set_uint8(x_250, sizeof(void*)*2, x_249);
x_251 = lean_unsigned_to_nat(0u);
x_252 = lean_array_get_size(x_236);
x_253 = lean_nat_dec_lt(x_251, x_252);
if (x_253 == 0)
{
lean_dec(x_252);
lean_dec(x_246);
lean_dec(x_238);
lean_dec(x_236);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_21 = x_239;
x_22 = x_250;
x_23 = x_241;
goto block_27;
}
else
{
uint8_t x_254; 
x_254 = lean_nat_dec_le(x_252, x_252);
if (x_254 == 0)
{
lean_dec(x_252);
lean_dec(x_246);
lean_dec(x_238);
lean_dec(x_236);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_21 = x_239;
x_22 = x_250;
x_23 = x_241;
goto block_27;
}
else
{
lean_object* x_255; size_t x_256; size_t x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_255 = lean_box(0);
x_256 = 0;
x_257 = lean_usize_of_nat(x_252);
lean_dec(x_252);
x_258 = l_Array_foldlMUnsafe_fold___redArg(x_246, x_238, x_236, x_256, x_257, x_255);
x_259 = lean_apply_7(x_258, x_7, x_8, x_9, x_10, x_11, x_250, x_241);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; lean_object* x_262; 
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec(x_259);
x_262 = lean_ctor_get(x_260, 1);
lean_inc(x_262);
lean_dec(x_260);
x_21 = x_239;
x_22 = x_262;
x_23 = x_261;
goto block_27;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_263 = lean_ctor_get(x_259, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 x_264 = x_259;
} else {
 lean_dec_ref(x_259);
 x_264 = lean_box(0);
}
x_265 = lean_ctor_get(x_260, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_260, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 x_267 = x_260;
} else {
 lean_dec_ref(x_260);
 x_267 = lean_box(0);
}
if (lean_is_scalar(x_267)) {
 x_268 = lean_alloc_ctor(1, 2, 0);
} else {
 x_268 = x_267;
}
lean_ctor_set(x_268, 0, x_265);
lean_ctor_set(x_268, 1, x_266);
if (lean_is_scalar(x_264)) {
 x_269 = lean_alloc_ctor(0, 2, 0);
} else {
 x_269 = x_264;
}
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_263);
return x_269;
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
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_285 = lean_ctor_get(x_28, 0);
x_286 = lean_ctor_get(x_28, 1);
lean_inc(x_286);
lean_inc(x_285);
lean_dec(x_28);
x_287 = lean_ctor_get(x_285, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_285, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 lean_ctor_release(x_285, 2);
 lean_ctor_release(x_285, 3);
 lean_ctor_release(x_285, 4);
 x_289 = x_285;
} else {
 lean_dec_ref(x_285);
 x_289 = lean_box(0);
}
lean_inc(x_286);
lean_inc(x_288);
x_290 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_290, 0, x_288);
lean_closure_set(x_290, 1, x_286);
lean_inc(x_286);
lean_inc(x_288);
x_291 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_291, 0, x_288);
lean_closure_set(x_291, 1, x_286);
lean_inc(x_290);
lean_inc(x_288);
x_292 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_292, 0, x_288);
lean_closure_set(x_292, 1, x_290);
lean_inc(x_288);
lean_inc(x_287);
x_293 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_293, 0, x_287);
lean_closure_set(x_293, 1, x_288);
lean_closure_set(x_293, 2, x_286);
x_294 = l_Lake_EStateT_instFunctor___redArg(x_287);
x_295 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_295, 0, x_288);
if (lean_is_scalar(x_289)) {
 x_296 = lean_alloc_ctor(0, 5, 0);
} else {
 x_296 = x_289;
}
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set(x_296, 1, x_295);
lean_ctor_set(x_296, 2, x_293);
lean_ctor_set(x_296, 3, x_292);
lean_ctor_set(x_296, 4, x_291);
x_297 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_290);
x_298 = l_ReaderT_instMonad___redArg(x_297);
x_299 = l_ReaderT_instMonad___redArg(x_298);
x_300 = l_ReaderT_instMonad___redArg(x_299);
x_301 = l_ReaderT_instMonad___redArg(x_300);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
lean_dec(x_301);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_302 = lean_ctor_get(x_4, 3);
x_303 = l_Lake_MTime_checkUpToDate___redArg(x_2, x_3, x_302, x_13);
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_303, 1);
lean_inc(x_305);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 lean_ctor_release(x_303, 1);
 x_306 = x_303;
} else {
 lean_dec_ref(x_303);
 x_306 = lean_box(0);
}
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_304);
lean_ctor_set(x_307, 1, x_12);
if (lean_is_scalar(x_306)) {
 x_308 = lean_alloc_ctor(0, 2, 0);
} else {
 x_308 = x_306;
}
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_305);
return x_308;
}
case 1:
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; lean_object* x_318; uint8_t x_319; 
lean_dec(x_301);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_309 = l_Lake_MTime_checkUpToDate___redArg(x_2, x_3, x_6, x_13);
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_309, 1);
lean_inc(x_311);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 lean_ctor_release(x_309, 1);
 x_312 = x_309;
} else {
 lean_dec_ref(x_309);
 x_312 = lean_box(0);
}
x_318 = lean_ctor_get(x_11, 0);
lean_inc(x_318);
lean_dec(x_11);
x_319 = lean_ctor_get_uint8(x_318, sizeof(void*)*1);
lean_dec(x_318);
if (x_319 == 0)
{
lean_dec(x_310);
x_313 = x_319;
goto block_317;
}
else
{
uint8_t x_320; 
x_320 = lean_unbox(x_310);
lean_dec(x_310);
x_313 = x_320;
goto block_317;
}
block_317:
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_314 = lean_box(x_313);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_12);
if (lean_is_scalar(x_312)) {
 x_316 = lean_alloc_ctor(0, 2, 0);
} else {
 x_316 = x_312;
}
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_311);
return x_316;
}
}
default: 
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; lean_object* x_328; lean_object* x_329; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; 
x_321 = lean_ctor_get(x_5, 0);
lean_inc(x_321);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_322 = x_5;
} else {
 lean_dec_ref(x_5);
 x_322 = lean_box(0);
}
x_323 = lean_ctor_get(x_321, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_321, 3);
lean_inc(x_324);
lean_dec(x_321);
x_325 = lean_ctor_get(x_4, 2);
x_326 = lean_alloc_closure((void*)(l_Lake_SavedTrace_replayIfUpToDate___redArg___lam__0___boxed), 9, 0);
if (lean_is_scalar(x_322)) {
 x_359 = lean_alloc_ctor(1, 1, 0);
} else {
 x_359 = x_322;
 lean_ctor_set_tag(x_359, 1);
}
lean_ctor_set(x_359, 0, x_323);
x_360 = l_Lake_checkHashUpToDate___redArg___closed__0;
lean_inc(x_325);
x_361 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_361, 0, x_325);
x_362 = l_Option_beqOption___redArg____x40_Init_Data_Option_Basic___hyg_160_(x_360, x_361, x_359);
if (x_362 == 0)
{
lean_object* x_363; uint8_t x_364; 
lean_dec(x_1);
x_363 = lean_ctor_get(x_11, 0);
lean_inc(x_363);
x_364 = lean_ctor_get_uint8(x_363, sizeof(void*)*1);
lean_dec(x_363);
if (x_364 == 0)
{
lean_dec(x_326);
lean_dec(x_324);
lean_dec(x_301);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_14 = x_364;
x_15 = x_12;
x_16 = x_13;
goto block_20;
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; 
x_365 = l_Lake_MTime_checkUpToDate___redArg(x_2, x_3, x_6, x_13);
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_365, 1);
lean_inc(x_367);
lean_dec(x_365);
x_368 = lean_unbox(x_366);
lean_dec(x_366);
x_327 = x_368;
x_328 = x_12;
x_329 = x_367;
goto block_358;
}
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; uint8_t x_372; 
lean_dec(x_2);
x_369 = lean_apply_2(x_1, x_3, x_13);
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_369, 1);
lean_inc(x_371);
lean_dec(x_369);
x_372 = lean_unbox(x_370);
lean_dec(x_370);
x_327 = x_372;
x_328 = x_12;
x_329 = x_371;
goto block_358;
}
block_358:
{
if (x_327 == 0)
{
lean_dec(x_326);
lean_dec(x_324);
lean_dec(x_301);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_14 = x_327;
x_15 = x_328;
x_16 = x_329;
goto block_20;
}
else
{
lean_object* x_330; uint8_t x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; uint8_t x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; uint8_t x_341; 
x_330 = lean_ctor_get(x_328, 0);
lean_inc(x_330);
x_331 = lean_ctor_get_uint8(x_328, sizeof(void*)*2);
x_332 = lean_ctor_get(x_328, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 lean_ctor_release(x_328, 1);
 x_333 = x_328;
} else {
 lean_dec_ref(x_328);
 x_333 = lean_box(0);
}
x_334 = l_Lake_EquipT_instMonad___redArg(x_301);
x_335 = lean_box(1);
x_336 = lean_unbox(x_335);
x_337 = l_Lake_JobAction_merge(x_331, x_336);
if (lean_is_scalar(x_333)) {
 x_338 = lean_alloc_ctor(0, 2, 1);
} else {
 x_338 = x_333;
}
lean_ctor_set(x_338, 0, x_330);
lean_ctor_set(x_338, 1, x_332);
lean_ctor_set_uint8(x_338, sizeof(void*)*2, x_337);
x_339 = lean_unsigned_to_nat(0u);
x_340 = lean_array_get_size(x_324);
x_341 = lean_nat_dec_lt(x_339, x_340);
if (x_341 == 0)
{
lean_dec(x_340);
lean_dec(x_334);
lean_dec(x_326);
lean_dec(x_324);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_21 = x_327;
x_22 = x_338;
x_23 = x_329;
goto block_27;
}
else
{
uint8_t x_342; 
x_342 = lean_nat_dec_le(x_340, x_340);
if (x_342 == 0)
{
lean_dec(x_340);
lean_dec(x_334);
lean_dec(x_326);
lean_dec(x_324);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_21 = x_327;
x_22 = x_338;
x_23 = x_329;
goto block_27;
}
else
{
lean_object* x_343; size_t x_344; size_t x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_343 = lean_box(0);
x_344 = 0;
x_345 = lean_usize_of_nat(x_340);
lean_dec(x_340);
x_346 = l_Array_foldlMUnsafe_fold___redArg(x_334, x_326, x_324, x_344, x_345, x_343);
x_347 = lean_apply_7(x_346, x_7, x_8, x_9, x_10, x_11, x_338, x_329);
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; 
x_349 = lean_ctor_get(x_347, 1);
lean_inc(x_349);
lean_dec(x_347);
x_350 = lean_ctor_get(x_348, 1);
lean_inc(x_350);
lean_dec(x_348);
x_21 = x_327;
x_22 = x_350;
x_23 = x_349;
goto block_27;
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_351 = lean_ctor_get(x_347, 1);
lean_inc(x_351);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 x_352 = x_347;
} else {
 lean_dec_ref(x_347);
 x_352 = lean_box(0);
}
x_353 = lean_ctor_get(x_348, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_348, 1);
lean_inc(x_354);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 x_355 = x_348;
} else {
 lean_dec_ref(x_348);
 x_355 = lean_box(0);
}
if (lean_is_scalar(x_355)) {
 x_356 = lean_alloc_ctor(1, 2, 0);
} else {
 x_356 = x_355;
}
lean_ctor_set(x_356, 0, x_353);
lean_ctor_set(x_356, 1, x_354);
if (lean_is_scalar(x_352)) {
 x_357 = lean_alloc_ctor(0, 2, 0);
} else {
 x_357 = x_352;
}
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_351);
return x_357;
}
}
}
}
}
}
}
}
block_20:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_box(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
block_27:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_box(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lake_SavedTrace_replayIfUpToDate___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_SavedTrace_replayIfUpToDate___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lake_SavedTrace_replayIfUpToDate___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lake_SavedTrace_replayIfUpToDate(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
lean_dec(x_5);
return x_15;
}
}
static uint8_t _init_l_Lake_buildAction___redArg___closed__0() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 3;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*1 + 2);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get_uint8(x_11, sizeof(void*)*2);
x_18 = l_Lake_JobAction_merge(x_17, x_5);
lean_inc(x_16);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_18);
x_19 = lean_apply_7(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
x_27 = lean_ctor_get_uint8(x_21, sizeof(void*)*2);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
x_29 = lean_array_get_size(x_16);
lean_dec(x_16);
x_30 = lean_array_get_size(x_26);
lean_inc(x_30);
x_31 = l_Array_extract___redArg(x_26, x_29, x_30);
lean_inc(x_24);
x_32 = lean_apply_1(x_1, x_24);
x_33 = l_Lake_writeTraceFile_go(x_3, x_2, x_32, x_31, x_22);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_26);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_20);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_20);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_24);
x_38 = !lean_is_exclusive(x_21);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_21, 1);
lean_dec(x_39);
x_40 = lean_ctor_get(x_21, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_33);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_33, 0);
x_43 = lean_io_error_to_string(x_42);
x_44 = lean_box(3);
x_45 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_45, 0, x_43);
x_46 = lean_unbox(x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_46);
x_47 = lean_array_push(x_26, x_45);
lean_ctor_set(x_21, 0, x_47);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 0, x_30);
lean_ctor_set_tag(x_33, 0);
lean_ctor_set(x_33, 0, x_20);
return x_33;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_48 = lean_ctor_get(x_33, 0);
x_49 = lean_ctor_get(x_33, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_33);
x_50 = lean_io_error_to_string(x_48);
x_51 = lean_box(3);
x_52 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_52, 0, x_50);
x_53 = lean_unbox(x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_53);
x_54 = lean_array_push(x_26, x_52);
lean_ctor_set(x_21, 0, x_54);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 0, x_30);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_20);
lean_ctor_set(x_55, 1, x_49);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_21);
x_56 = lean_ctor_get(x_33, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_33, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_58 = x_33;
} else {
 lean_dec_ref(x_33);
 x_58 = lean_box(0);
}
x_59 = lean_io_error_to_string(x_56);
x_60 = lean_box(3);
x_61 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_61, 0, x_59);
x_62 = lean_unbox(x_60);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_62);
x_63 = lean_array_push(x_26, x_61);
x_64 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_28);
lean_ctor_set_uint8(x_64, sizeof(void*)*2, x_27);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 1, x_64);
lean_ctor_set(x_20, 0, x_30);
if (lean_is_scalar(x_58)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_58;
 lean_ctor_set_tag(x_65, 0);
}
lean_ctor_set(x_65, 0, x_20);
lean_ctor_set(x_65, 1, x_57);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_66 = lean_ctor_get(x_20, 0);
lean_inc(x_66);
lean_dec(x_20);
x_67 = lean_ctor_get(x_21, 0);
lean_inc(x_67);
x_68 = lean_ctor_get_uint8(x_21, sizeof(void*)*2);
x_69 = lean_ctor_get(x_21, 1);
lean_inc(x_69);
x_70 = lean_array_get_size(x_16);
lean_dec(x_16);
x_71 = lean_array_get_size(x_67);
lean_inc(x_71);
x_72 = l_Array_extract___redArg(x_67, x_70, x_71);
lean_inc(x_66);
x_73 = lean_apply_1(x_1, x_66);
x_74 = l_Lake_writeTraceFile_go(x_3, x_2, x_73, x_72, x_22);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_71);
lean_dec(x_69);
lean_dec(x_67);
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
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_66);
lean_ctor_set(x_77, 1, x_21);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_66);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_79 = x_21;
} else {
 lean_dec_ref(x_21);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_74, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_74, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_82 = x_74;
} else {
 lean_dec_ref(x_74);
 x_82 = lean_box(0);
}
x_83 = lean_io_error_to_string(x_80);
x_84 = lean_box(3);
x_85 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_85, 0, x_83);
x_86 = lean_unbox(x_84);
lean_ctor_set_uint8(x_85, sizeof(void*)*1, x_86);
x_87 = lean_array_push(x_67, x_85);
if (lean_is_scalar(x_79)) {
 x_88 = lean_alloc_ctor(0, 2, 1);
} else {
 x_88 = x_79;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_69);
lean_ctor_set_uint8(x_88, sizeof(void*)*2, x_68);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_71);
lean_ctor_set(x_89, 1, x_88);
if (lean_is_scalar(x_82)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_82;
 lean_ctor_set_tag(x_90, 0);
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_81);
return x_90;
}
}
}
else
{
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_2);
lean_dec(x_1);
return x_19;
}
}
else
{
lean_object* x_91; uint8_t x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_91 = lean_ctor_get(x_11, 0);
x_92 = lean_ctor_get_uint8(x_11, sizeof(void*)*2);
x_93 = lean_ctor_get(x_11, 1);
lean_inc(x_93);
lean_inc(x_91);
lean_dec(x_11);
x_94 = l_Lake_JobAction_merge(x_92, x_5);
lean_inc(x_91);
x_95 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_95, 0, x_91);
lean_ctor_set(x_95, 1, x_93);
lean_ctor_set_uint8(x_95, sizeof(void*)*2, x_94);
x_96 = lean_apply_7(x_4, x_6, x_7, x_8, x_9, x_10, x_95, x_12);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_dec(x_96);
x_100 = lean_ctor_get(x_97, 0);
lean_inc(x_100);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_101 = x_97;
} else {
 lean_dec_ref(x_97);
 x_101 = lean_box(0);
}
x_102 = lean_ctor_get(x_98, 0);
lean_inc(x_102);
x_103 = lean_ctor_get_uint8(x_98, sizeof(void*)*2);
x_104 = lean_ctor_get(x_98, 1);
lean_inc(x_104);
x_105 = lean_array_get_size(x_91);
lean_dec(x_91);
x_106 = lean_array_get_size(x_102);
lean_inc(x_106);
x_107 = l_Array_extract___redArg(x_102, x_105, x_106);
lean_inc(x_100);
x_108 = lean_apply_1(x_1, x_100);
x_109 = l_Lake_writeTraceFile_go(x_3, x_2, x_108, x_107, x_99);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_106);
lean_dec(x_104);
lean_dec(x_102);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_111 = x_109;
} else {
 lean_dec_ref(x_109);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_101;
}
lean_ctor_set(x_112, 0, x_100);
lean_ctor_set(x_112, 1, x_98);
if (lean_is_scalar(x_111)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_111;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_110);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_100);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_114 = x_98;
} else {
 lean_dec_ref(x_98);
 x_114 = lean_box(0);
}
x_115 = lean_ctor_get(x_109, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_109, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_117 = x_109;
} else {
 lean_dec_ref(x_109);
 x_117 = lean_box(0);
}
x_118 = lean_io_error_to_string(x_115);
x_119 = lean_box(3);
x_120 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_120, 0, x_118);
x_121 = lean_unbox(x_119);
lean_ctor_set_uint8(x_120, sizeof(void*)*1, x_121);
x_122 = lean_array_push(x_102, x_120);
if (lean_is_scalar(x_114)) {
 x_123 = lean_alloc_ctor(0, 2, 1);
} else {
 x_123 = x_114;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_104);
lean_ctor_set_uint8(x_123, sizeof(void*)*2, x_103);
if (lean_is_scalar(x_101)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_101;
 lean_ctor_set_tag(x_124, 1);
}
lean_ctor_set(x_124, 0, x_106);
lean_ctor_set(x_124, 1, x_123);
if (lean_is_scalar(x_117)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_117;
 lean_ctor_set_tag(x_125, 0);
}
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_116);
return x_125;
}
}
else
{
lean_dec(x_97);
lean_dec(x_91);
lean_dec(x_2);
lean_dec(x_1);
return x_96;
}
}
}
else
{
lean_object* x_126; uint8_t x_127; lean_object* x_128; uint8_t x_129; lean_object* x_130; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_126 = lean_ctor_get(x_11, 0);
lean_inc(x_126);
x_127 = lean_ctor_get_uint8(x_11, sizeof(void*)*2);
x_128 = lean_ctor_get(x_11, 1);
lean_inc(x_128);
x_129 = l_Lake_buildAction___redArg___closed__0;
x_130 = lean_io_exit(x_129, x_12);
if (lean_obj_tag(x_130) == 0)
{
uint8_t x_131; 
lean_dec(x_128);
lean_dec(x_126);
x_131 = !lean_is_exclusive(x_130);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_130, 0);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_11);
lean_ctor_set(x_130, 0, x_133);
return x_130;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_134 = lean_ctor_get(x_130, 0);
x_135 = lean_ctor_get(x_130, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_130);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_11);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
else
{
uint8_t x_138; 
x_138 = !lean_is_exclusive(x_11);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_139 = lean_ctor_get(x_11, 1);
lean_dec(x_139);
x_140 = lean_ctor_get(x_11, 0);
lean_dec(x_140);
x_141 = !lean_is_exclusive(x_130);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_142 = lean_ctor_get(x_130, 0);
x_143 = lean_io_error_to_string(x_142);
x_144 = lean_box(3);
x_145 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_145, 0, x_143);
x_146 = lean_unbox(x_144);
lean_ctor_set_uint8(x_145, sizeof(void*)*1, x_146);
x_147 = lean_array_get_size(x_126);
x_148 = lean_array_push(x_126, x_145);
lean_ctor_set(x_11, 0, x_148);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_11);
lean_ctor_set_tag(x_130, 0);
lean_ctor_set(x_130, 0, x_149);
return x_130;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_150 = lean_ctor_get(x_130, 0);
x_151 = lean_ctor_get(x_130, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_130);
x_152 = lean_io_error_to_string(x_150);
x_153 = lean_box(3);
x_154 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_154, 0, x_152);
x_155 = lean_unbox(x_153);
lean_ctor_set_uint8(x_154, sizeof(void*)*1, x_155);
x_156 = lean_array_get_size(x_126);
x_157 = lean_array_push(x_126, x_154);
lean_ctor_set(x_11, 0, x_157);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_11);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_151);
return x_159;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_11);
x_160 = lean_ctor_get(x_130, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_130, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_162 = x_130;
} else {
 lean_dec_ref(x_130);
 x_162 = lean_box(0);
}
x_163 = lean_io_error_to_string(x_160);
x_164 = lean_box(3);
x_165 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_165, 0, x_163);
x_166 = lean_unbox(x_164);
lean_ctor_set_uint8(x_165, sizeof(void*)*1, x_166);
x_167 = lean_array_get_size(x_126);
x_168 = lean_array_push(x_126, x_165);
x_169 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_128);
lean_ctor_set_uint8(x_169, sizeof(void*)*2, x_127);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_167);
lean_ctor_set(x_170, 1, x_169);
if (lean_is_scalar(x_162)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_162;
 lean_ctor_set_tag(x_171, 0);
}
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_161);
return x_171;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lake_buildAction___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Lake_buildAction___redArg(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_6);
lean_dec(x_6);
x_15 = l_Lake_buildAction(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
return x_15;
}
}
static lean_object* _init_l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instToJsonPUnit__lake___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_5);
x_18 = l_Lake_readTraceFile(x_5, x_17, x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
lean_ctor_set(x_14, 0, x_22);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_23 = l_Lake_SavedTrace_replayIfUpToDate___redArg(x_1, x_2, x_3, x_4, x_21, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_20);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0;
x_30 = l_Lake_buildAction___redArg(x_29, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_28, x_27);
lean_dec(x_5);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_31, 0);
lean_dec(x_35);
lean_ctor_set(x_31, 0, x_25);
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_25);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_30, 0, x_37);
return x_30;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_dec(x_30);
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_40 = x_31;
} else {
 lean_dec_ref(x_31);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_25);
lean_ctor_set(x_41, 1, x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_38);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_25);
x_43 = !lean_is_exclusive(x_30);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_30, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_31);
if (x_45 == 0)
{
return x_30;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_31, 0);
x_47 = lean_ctor_get(x_31, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_31);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_30, 0, x_48);
return x_30;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_30, 1);
lean_inc(x_49);
lean_dec(x_30);
x_50 = lean_ctor_get(x_31, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_31, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_52 = x_31;
} else {
 lean_dec_ref(x_31);
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
return x_54;
}
}
}
else
{
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_23;
}
}
else
{
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_23;
}
}
else
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_55 = lean_ctor_get(x_14, 0);
x_56 = lean_ctor_get_uint8(x_14, sizeof(void*)*2);
x_57 = lean_ctor_get(x_14, 1);
lean_inc(x_57);
lean_inc(x_55);
lean_dec(x_14);
lean_inc(x_5);
x_58 = l_Lake_readTraceFile(x_5, x_55, x_15);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_57);
lean_ctor_set_uint8(x_63, sizeof(void*)*2, x_56);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_64 = l_Lake_SavedTrace_replayIfUpToDate___redArg(x_1, x_2, x_3, x_4, x_61, x_8, x_9, x_10, x_11, x_12, x_13, x_63, x_60);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_unbox(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_64, 1);
lean_inc(x_68);
lean_dec(x_64);
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
lean_dec(x_65);
x_70 = l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0;
x_71 = l_Lake_buildAction___redArg(x_70, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_69, x_68);
lean_dec(x_5);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_74 = x_71;
} else {
 lean_dec_ref(x_71);
 x_74 = lean_box(0);
}
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
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_66);
lean_ctor_set(x_77, 1, x_75);
if (lean_is_scalar(x_74)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_74;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_73);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_66);
x_79 = lean_ctor_get(x_71, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_80 = x_71;
} else {
 lean_dec_ref(x_71);
 x_80 = lean_box(0);
}
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
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
if (lean_is_scalar(x_80)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_80;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_79);
return x_85;
}
}
else
{
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_64;
}
}
else
{
lean_dec(x_65);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_64;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_6);
x_19 = l_Lake_readTraceFile(x_6, x_18, x_16);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
lean_ctor_set(x_15, 0, x_23);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_24 = l_Lake_SavedTrace_replayIfUpToDate___redArg(x_2, x_3, x_4, x_5, x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_21);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0;
x_31 = l_Lake_buildAction___redArg(x_30, x_5, x_6, x_7, x_8, x_10, x_11, x_12, x_13, x_14, x_29, x_28);
lean_dec(x_6);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_32, 0);
lean_dec(x_36);
lean_ctor_set(x_32, 0, x_26);
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_26);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_31, 0, x_38);
return x_31;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_dec(x_31);
x_40 = lean_ctor_get(x_32, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_41 = x_32;
} else {
 lean_dec_ref(x_32);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_26);
lean_ctor_set(x_42, 1, x_40);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_26);
x_44 = !lean_is_exclusive(x_31);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_31, 0);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_32);
if (x_46 == 0)
{
return x_31;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_32, 0);
x_48 = lean_ctor_get(x_32, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_32);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_31, 0, x_49);
return x_31;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_31, 1);
lean_inc(x_50);
lean_dec(x_31);
x_51 = lean_ctor_get(x_32, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_32, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_53 = x_32;
} else {
 lean_dec_ref(x_32);
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
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_24;
}
}
else
{
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_24;
}
}
else
{
lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_56 = lean_ctor_get(x_15, 0);
x_57 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
x_58 = lean_ctor_get(x_15, 1);
lean_inc(x_58);
lean_inc(x_56);
lean_dec(x_15);
lean_inc(x_6);
x_59 = l_Lake_readTraceFile(x_6, x_56, x_16);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_58);
lean_ctor_set_uint8(x_64, sizeof(void*)*2, x_57);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_65 = l_Lake_SavedTrace_replayIfUpToDate___redArg(x_2, x_3, x_4, x_5, x_62, x_9, x_10, x_11, x_12, x_13, x_14, x_64, x_61);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_unbox(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
lean_dec(x_65);
x_70 = lean_ctor_get(x_66, 1);
lean_inc(x_70);
lean_dec(x_66);
x_71 = l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0;
x_72 = l_Lake_buildAction___redArg(x_71, x_5, x_6, x_7, x_8, x_10, x_11, x_12, x_13, x_14, x_70, x_69);
lean_dec(x_6);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_75 = x_72;
} else {
 lean_dec_ref(x_72);
 x_75 = lean_box(0);
}
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
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_67);
lean_ctor_set(x_78, 1, x_76);
if (lean_is_scalar(x_75)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_75;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_74);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_67);
x_80 = lean_ctor_get(x_72, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_81 = x_72;
} else {
 lean_dec_ref(x_72);
 x_81 = lean_box(0);
}
x_82 = lean_ctor_get(x_73, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_73, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_84 = x_73;
} else {
 lean_dec_ref(x_73);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
if (lean_is_scalar(x_81)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_81;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_80);
return x_86;
}
}
else
{
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_65;
}
}
else
{
lean_dec(x_66);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_65;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_7);
lean_dec(x_7);
x_17 = l_Lake_buildUnlessUpToDate_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_8);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_8);
lean_dec(x_8);
x_18 = l_Lake_buildUnlessUpToDate_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_17, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_9);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_22; 
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_40; 
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_5);
x_24 = l_Lake_readTraceFile(x_5, x_23, x_15);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_30 = x_25;
} else {
 lean_dec_ref(x_25);
 x_30 = lean_box(0);
}
lean_ctor_set(x_14, 0, x_29);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_31 = l_Lake_SavedTrace_replayIfUpToDate___redArg(x_1, x_2, x_3, x_4, x_28, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_26);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
x_34 = lean_box(0);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_32, 0);
lean_inc(x_48);
x_49 = lean_unbox(x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_31);
x_50 = lean_ctor_get(x_32, 1);
lean_inc(x_50);
lean_dec(x_32);
x_51 = l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0;
x_52 = l_Lake_buildAction___redArg(x_51, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_50, x_33);
lean_dec(x_5);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_35 = x_55;
x_36 = x_54;
goto block_39;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_30);
lean_dec(x_27);
x_56 = lean_ctor_get(x_52, 1);
lean_inc(x_56);
lean_dec(x_52);
x_57 = lean_ctor_get(x_53, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
lean_dec(x_53);
x_16 = x_57;
x_17 = x_58;
x_18 = x_56;
goto block_21;
}
}
else
{
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_40 = x_31;
goto block_47;
}
}
else
{
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_40 = x_31;
goto block_47;
}
block_39:
{
lean_object* x_37; lean_object* x_38; 
if (lean_is_scalar(x_30)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_30;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
if (lean_is_scalar(x_27)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_27;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
block_47:
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_35 = x_43;
x_36 = x_42;
goto block_39;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_30);
lean_dec(x_27);
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_ctor_get(x_41, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_dec(x_41);
x_16 = x_45;
x_17 = x_46;
x_18 = x_44;
goto block_21;
}
}
}
else
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_79; 
x_59 = lean_ctor_get(x_14, 0);
x_60 = lean_ctor_get_uint8(x_14, sizeof(void*)*2);
x_61 = lean_ctor_get(x_14, 1);
lean_inc(x_61);
lean_inc(x_59);
lean_dec(x_14);
lean_inc(x_5);
x_62 = l_Lake_readTraceFile(x_5, x_59, x_15);
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
x_66 = lean_ctor_get(x_63, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_68 = x_63;
} else {
 lean_dec_ref(x_63);
 x_68 = lean_box(0);
}
x_69 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_61);
lean_ctor_set_uint8(x_69, sizeof(void*)*2, x_60);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_70 = l_Lake_SavedTrace_replayIfUpToDate___redArg(x_1, x_2, x_3, x_4, x_66, x_8, x_9, x_10, x_11, x_12, x_13, x_69, x_64);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
x_73 = lean_box(0);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_71, 0);
lean_inc(x_87);
x_88 = lean_unbox(x_87);
lean_dec(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_70);
x_89 = lean_ctor_get(x_71, 1);
lean_inc(x_89);
lean_dec(x_71);
x_90 = l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0;
x_91 = l_Lake_buildAction___redArg(x_90, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_89, x_72);
lean_dec(x_5);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_74 = x_94;
x_75 = x_93;
goto block_78;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_68);
lean_dec(x_65);
x_95 = lean_ctor_get(x_91, 1);
lean_inc(x_95);
lean_dec(x_91);
x_96 = lean_ctor_get(x_92, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_92, 1);
lean_inc(x_97);
lean_dec(x_92);
x_16 = x_96;
x_17 = x_97;
x_18 = x_95;
goto block_21;
}
}
else
{
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_79 = x_70;
goto block_86;
}
}
else
{
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_79 = x_70;
goto block_86;
}
block_78:
{
lean_object* x_76; lean_object* x_77; 
if (lean_is_scalar(x_68)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_68;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
if (lean_is_scalar(x_65)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_65;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
block_86:
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_74 = x_82;
x_75 = x_81;
goto block_78;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_68);
lean_dec(x_65);
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
lean_dec(x_79);
x_84 = lean_ctor_get(x_80, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_80, 1);
lean_inc(x_85);
lean_dec(x_80);
x_16 = x_84;
x_17 = x_85;
x_18 = x_83;
goto block_21;
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
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_23; 
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_41; 
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_6);
x_25 = l_Lake_readTraceFile(x_6, x_24, x_16);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_28 = x_25;
} else {
 lean_dec_ref(x_25);
 x_28 = lean_box(0);
}
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_31 = x_26;
} else {
 lean_dec_ref(x_26);
 x_31 = lean_box(0);
}
lean_ctor_set(x_15, 0, x_30);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_32 = l_Lake_SavedTrace_replayIfUpToDate___redArg(x_2, x_3, x_4, x_5, x_29, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_27);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
x_35 = lean_box(0);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_33, 0);
lean_inc(x_49);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_32);
x_51 = lean_ctor_get(x_33, 1);
lean_inc(x_51);
lean_dec(x_33);
x_52 = l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0;
x_53 = l_Lake_buildAction___redArg(x_52, x_5, x_6, x_7, x_8, x_10, x_11, x_12, x_13, x_14, x_51, x_34);
lean_dec(x_6);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_36 = x_56;
x_37 = x_55;
goto block_40;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_31);
lean_dec(x_28);
x_57 = lean_ctor_get(x_53, 1);
lean_inc(x_57);
lean_dec(x_53);
x_58 = lean_ctor_get(x_54, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_dec(x_54);
x_17 = x_58;
x_18 = x_59;
x_19 = x_57;
goto block_22;
}
}
else
{
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_41 = x_32;
goto block_48;
}
}
else
{
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_41 = x_32;
goto block_48;
}
block_40:
{
lean_object* x_38; lean_object* x_39; 
if (lean_is_scalar(x_31)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_31;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
if (lean_is_scalar(x_28)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_28;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
block_48:
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_36 = x_44;
x_37 = x_43;
goto block_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_31);
lean_dec(x_28);
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_ctor_get(x_42, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
lean_dec(x_42);
x_17 = x_46;
x_18 = x_47;
x_19 = x_45;
goto block_22;
}
}
}
else
{
lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_80; 
x_60 = lean_ctor_get(x_15, 0);
x_61 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
x_62 = lean_ctor_get(x_15, 1);
lean_inc(x_62);
lean_inc(x_60);
lean_dec(x_15);
lean_inc(x_6);
x_63 = l_Lake_readTraceFile(x_6, x_60, x_16);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
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
x_70 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_62);
lean_ctor_set_uint8(x_70, sizeof(void*)*2, x_61);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_71 = l_Lake_SavedTrace_replayIfUpToDate___redArg(x_2, x_3, x_4, x_5, x_67, x_9, x_10, x_11, x_12, x_13, x_14, x_70, x_65);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
x_74 = lean_box(0);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_72, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
lean_dec(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_71);
x_90 = lean_ctor_get(x_72, 1);
lean_inc(x_90);
lean_dec(x_72);
x_91 = l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0;
x_92 = l_Lake_buildAction___redArg(x_91, x_5, x_6, x_7, x_8, x_10, x_11, x_12, x_13, x_14, x_90, x_73);
lean_dec(x_6);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_75 = x_95;
x_76 = x_94;
goto block_79;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_69);
lean_dec(x_66);
x_96 = lean_ctor_get(x_92, 1);
lean_inc(x_96);
lean_dec(x_92);
x_97 = lean_ctor_get(x_93, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_93, 1);
lean_inc(x_98);
lean_dec(x_93);
x_17 = x_97;
x_18 = x_98;
x_19 = x_96;
goto block_22;
}
}
else
{
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_80 = x_71;
goto block_87;
}
}
else
{
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_80 = x_71;
goto block_87;
}
block_79:
{
lean_object* x_77; lean_object* x_78; 
if (lean_is_scalar(x_69)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_69;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
if (lean_is_scalar(x_66)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_66;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
block_87:
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_75 = x_83;
x_76 = x_82;
goto block_79;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_69);
lean_dec(x_66);
x_84 = lean_ctor_get(x_80, 1);
lean_inc(x_84);
lean_dec(x_80);
x_85 = lean_ctor_get(x_81, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_81, 1);
lean_inc(x_86);
lean_dec(x_81);
x_17 = x_85;
x_18 = x_86;
x_19 = x_84;
goto block_22;
}
}
}
block_22:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_7);
lean_dec(x_7);
x_17 = l_Lake_buildUnlessUpToDate___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_8);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_8);
lean_dec(x_8);
x_18 = l_Lake_buildUnlessUpToDate(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_17, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_9);
return x_18;
}
}
static lean_object* _init_l_Lake_writeFileHash___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".hash", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_writeFileHash(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lake_writeFileHash___closed__0;
x_5 = lean_string_append(x_1, x_4);
x_6 = l_Lake_createParentDirs(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_uint64_to_nat(x_2);
x_9 = l_Nat_reprFast(x_8);
x_10 = l_IO_FS_writeFile(x_5, x_9, x_7);
lean_dec(x_9);
lean_dec(x_5);
return x_10;
}
else
{
lean_dec(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lake_writeFileHash___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Lake_writeFileHash(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheFileHash(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
if (x_2 == 0)
{
lean_object* x_14; 
x_14 = l_Lake_computeBinFileHash(x_1, x_3);
x_4 = x_14;
goto block_13;
}
else
{
lean_object* x_15; 
x_15 = l_Lake_computeTextFileHash(x_1, x_3);
x_4 = x_15;
goto block_13;
}
block_13:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_unbox_uint64(x_5);
lean_dec(x_5);
x_8 = l_Lake_writeFileHash(x_1, x_7, x_6);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_cacheFileHash___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_cacheFileHash(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_clearFileHash(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lake_writeFileHash___closed__0;
x_4 = lean_string_append(x_1, x_3);
x_5 = lean_io_remove_file(x_4, x_2);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 11)
{
uint8_t x_7; 
lean_dec(x_6);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
lean_dec(x_6);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_94; lean_object* x_95; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 1);
x_8 = l_Lake_writeFileHash___closed__0;
lean_inc(x_1);
x_9 = lean_string_append(x_1, x_8);
if (x_7 == 0)
{
x_94 = x_4;
x_95 = x_5;
goto block_104;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = l_Lake_Hash_load_x3f(x_9, x_5);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_94 = x_4;
x_95 = x_107;
goto block_104;
}
else
{
uint8_t x_108; 
lean_dec(x_9);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_105);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_105, 0);
lean_dec(x_109);
x_110 = lean_ctor_get(x_106, 0);
lean_inc(x_110);
lean_dec(x_106);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_4);
lean_ctor_set(x_105, 0, x_111);
return x_105;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_105, 1);
lean_inc(x_112);
lean_dec(x_105);
x_113 = lean_ctor_get(x_106, 0);
lean_inc(x_113);
lean_dec(x_106);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_4);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_112);
return x_115;
}
}
}
block_93:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lake_createParentDirs(x_9, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint64_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_unbox_uint64(x_14);
x_19 = lean_uint64_to_nat(x_18);
x_20 = l_Nat_reprFast(x_19);
x_21 = l_IO_FS_writeFile(x_9, x_20, x_17);
lean_dec(x_20);
lean_dec(x_9);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_11);
lean_ctor_set_uint8(x_24, sizeof(void*)*2, x_10);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_11);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_10);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_14);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_14);
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_21, 0);
x_32 = lean_io_error_to_string(x_31);
x_33 = lean_box(3);
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_32);
x_35 = lean_unbox(x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_35);
x_36 = lean_array_get_size(x_12);
x_37 = lean_array_push(x_12, x_34);
x_38 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_11);
lean_ctor_set_uint8(x_38, sizeof(void*)*2, x_10);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set_tag(x_21, 0);
lean_ctor_set(x_21, 0, x_39);
return x_21;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_40 = lean_ctor_get(x_21, 0);
x_41 = lean_ctor_get(x_21, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_21);
x_42 = lean_io_error_to_string(x_40);
x_43 = lean_box(3);
x_44 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_44, 0, x_42);
x_45 = lean_unbox(x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_45);
x_46 = lean_array_get_size(x_12);
x_47 = lean_array_push(x_12, x_44);
x_48 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_11);
lean_ctor_set_uint8(x_48, sizeof(void*)*2, x_10);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_41);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_14);
lean_dec(x_9);
x_51 = !lean_is_exclusive(x_16);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get(x_16, 0);
x_53 = lean_io_error_to_string(x_52);
x_54 = lean_box(3);
x_55 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_55, 0, x_53);
x_56 = lean_unbox(x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_56);
x_57 = lean_array_get_size(x_12);
x_58 = lean_array_push(x_12, x_55);
x_59 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_11);
lean_ctor_set_uint8(x_59, sizeof(void*)*2, x_10);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set_tag(x_16, 0);
lean_ctor_set(x_16, 0, x_60);
return x_16;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_61 = lean_ctor_get(x_16, 0);
x_62 = lean_ctor_get(x_16, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_16);
x_63 = lean_io_error_to_string(x_61);
x_64 = lean_box(3);
x_65 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_65, 0, x_63);
x_66 = lean_unbox(x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_66);
x_67 = lean_array_get_size(x_12);
x_68 = lean_array_push(x_12, x_65);
x_69 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_11);
lean_ctor_set_uint8(x_69, sizeof(void*)*2, x_10);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_62);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_9);
x_72 = !lean_is_exclusive(x_13);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_73 = lean_ctor_get(x_13, 0);
x_74 = lean_io_error_to_string(x_73);
x_75 = lean_box(3);
x_76 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_76, 0, x_74);
x_77 = lean_unbox(x_75);
lean_ctor_set_uint8(x_76, sizeof(void*)*1, x_77);
x_78 = lean_array_get_size(x_12);
x_79 = lean_array_push(x_12, x_76);
x_80 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_11);
lean_ctor_set_uint8(x_80, sizeof(void*)*2, x_10);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_80);
lean_ctor_set_tag(x_13, 0);
lean_ctor_set(x_13, 0, x_81);
return x_13;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_82 = lean_ctor_get(x_13, 0);
x_83 = lean_ctor_get(x_13, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_13);
x_84 = lean_io_error_to_string(x_82);
x_85 = lean_box(3);
x_86 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_86, 0, x_84);
x_87 = lean_unbox(x_85);
lean_ctor_set_uint8(x_86, sizeof(void*)*1, x_87);
x_88 = lean_array_get_size(x_12);
x_89 = lean_array_push(x_12, x_86);
x_90 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_11);
lean_ctor_set_uint8(x_90, sizeof(void*)*2, x_10);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_83);
return x_92;
}
}
}
block_104:
{
if (x_2 == 0)
{
lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
x_97 = lean_ctor_get_uint8(x_94, sizeof(void*)*2);
x_98 = lean_ctor_get(x_94, 1);
lean_inc(x_98);
lean_dec(x_94);
x_99 = l_Lake_computeBinFileHash(x_1, x_95);
lean_dec(x_1);
x_10 = x_97;
x_11 = x_98;
x_12 = x_96;
x_13 = x_99;
goto block_93;
}
else
{
lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_94, 0);
lean_inc(x_100);
x_101 = lean_ctor_get_uint8(x_94, sizeof(void*)*2);
x_102 = lean_ctor_get(x_94, 1);
lean_inc(x_102);
lean_dec(x_94);
x_103 = l_Lake_computeTextFileHash(x_1, x_95);
lean_dec(x_1);
x_10 = x_101;
x_11 = x_102;
x_12 = x_100;
x_13 = x_103;
goto block_93;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_fetchFileHash___redArg(x_1, x_2, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lake_fetchFileHash___redArg(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lake_fetchFileHash(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_6 = l_Lake_fetchFileHash___redArg(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
x_16 = lean_io_metadata(x_1, x_9);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_15);
lean_dec(x_13);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lake_platformTrace___closed__2;
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_11);
lean_ctor_set(x_21, 3, x_19);
lean_ctor_set(x_7, 0, x_21);
lean_ctor_set(x_16, 0, x_7);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lake_platformTrace___closed__2;
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_11);
lean_ctor_set(x_26, 3, x_24);
lean_ctor_set(x_7, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_7);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_11);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_8);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_8, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_8, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_16, 0);
x_33 = lean_io_error_to_string(x_32);
x_34 = lean_box(3);
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
x_36 = lean_unbox(x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_36);
x_37 = lean_array_get_size(x_13);
x_38 = lean_array_push(x_13, x_35);
lean_ctor_set(x_8, 0, x_38);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_37);
lean_ctor_set_tag(x_16, 0);
lean_ctor_set(x_16, 0, x_7);
return x_16;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_16, 0);
x_40 = lean_ctor_get(x_16, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_16);
x_41 = lean_io_error_to_string(x_39);
x_42 = lean_box(3);
x_43 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_43, 0, x_41);
x_44 = lean_unbox(x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_44);
x_45 = lean_array_get_size(x_13);
x_46 = lean_array_push(x_13, x_43);
lean_ctor_set(x_8, 0, x_46);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_7);
lean_ctor_set(x_47, 1, x_40);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_8);
x_48 = lean_ctor_get(x_16, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_16, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_50 = x_16;
} else {
 lean_dec_ref(x_16);
 x_50 = lean_box(0);
}
x_51 = lean_io_error_to_string(x_48);
x_52 = lean_box(3);
x_53 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_53, 0, x_51);
x_54 = lean_unbox(x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_54);
x_55 = lean_array_get_size(x_13);
x_56 = lean_array_push(x_13, x_53);
x_57 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_15);
lean_ctor_set_uint8(x_57, sizeof(void*)*2, x_14);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_57);
lean_ctor_set(x_7, 0, x_55);
if (lean_is_scalar(x_50)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_50;
 lean_ctor_set_tag(x_58, 0);
}
lean_ctor_set(x_58, 0, x_7);
lean_ctor_set(x_58, 1, x_49);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_7, 0);
lean_inc(x_59);
lean_dec(x_7);
x_60 = lean_ctor_get(x_8, 0);
lean_inc(x_60);
x_61 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
x_62 = lean_ctor_get(x_8, 1);
lean_inc(x_62);
x_63 = lean_io_metadata(x_1, x_9);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_62);
lean_dec(x_60);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = l_Lake_platformTrace___closed__2;
x_69 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set(x_69, 2, x_59);
lean_ctor_set(x_69, 3, x_67);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_8);
if (lean_is_scalar(x_66)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_66;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_65);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_59);
lean_dec(x_1);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_72 = x_8;
} else {
 lean_dec_ref(x_8);
 x_72 = lean_box(0);
}
x_73 = lean_ctor_get(x_63, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_63, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_75 = x_63;
} else {
 lean_dec_ref(x_63);
 x_75 = lean_box(0);
}
x_76 = lean_io_error_to_string(x_73);
x_77 = lean_box(3);
x_78 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_78, 0, x_76);
x_79 = lean_unbox(x_77);
lean_ctor_set_uint8(x_78, sizeof(void*)*1, x_79);
x_80 = lean_array_get_size(x_60);
x_81 = lean_array_push(x_60, x_78);
if (lean_is_scalar(x_72)) {
 x_82 = lean_alloc_ctor(0, 2, 1);
} else {
 x_82 = x_72;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_62);
lean_ctor_set_uint8(x_82, sizeof(void*)*2, x_61);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_82);
if (lean_is_scalar(x_75)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_75;
 lean_ctor_set_tag(x_84, 0);
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_74);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_6);
if (x_85 == 0)
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_6, 0);
lean_dec(x_86);
x_87 = !lean_is_exclusive(x_7);
if (x_87 == 0)
{
return x_6;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_7, 0);
x_89 = lean_ctor_get(x_7, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_7);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_6, 0, x_90);
return x_6;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_91 = lean_ctor_get(x_6, 1);
lean_inc(x_91);
lean_dec(x_6);
x_92 = lean_ctor_get(x_7, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_7, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_94 = x_7;
} else {
 lean_dec_ref(x_7);
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
return x_96;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_fetchFileTrace___redArg(x_1, x_2, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lake_fetchFileTrace___redArg(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lake_fetchFileTrace(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_IO_FS_ordSystemTime____x40_Init_System_IO___hyg_3236_(x_2, x_7);
lean_dec(x_7);
x_9 = lean_box(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_box(1);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; 
lean_dec(x_9);
x_11 = lean_box(0);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_IO_FS_ordSystemTime____x40_Init_System_IO___hyg_3236_(x_2, x_14);
lean_dec(x_14);
x_16 = lean_box(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_13);
return x_20;
}
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_4);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_4, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_23);
return x_4;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_dec(x_4);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_4);
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
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get_uint8(x_5, sizeof(void*)*2);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_inc(x_16);
lean_dec(x_5);
x_19 = lean_array_uget(x_1, x_2);
x_20 = lean_box(0);
x_21 = lean_array_push(x_16, x_19);
x_22 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_17);
x_23 = 1;
x_24 = lean_usize_add(x_2, x_23);
x_2 = x_24;
x_4 = x_20;
x_5 = x_22;
goto _start;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_5);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_6);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_unbox_uint64(x_9);
lean_dec(x_9);
x_12 = lean_unbox_uint64(x_10);
lean_dec(x_10);
x_13 = lean_uint64_dec_eq(x_11, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_3, 3);
x_27 = l_Lake_MTime_checkUpToDate___at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(x_2, x_26, x_11);
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
x_35 = l_Lake_MTime_checkUpToDate___at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(x_2, x_5, x_11);
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
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_48 = lean_ctor_get(x_4, 0);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 3);
lean_inc(x_50);
lean_dec(x_48);
x_89 = lean_ctor_get(x_3, 2);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_49);
lean_inc(x_89);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__2(x_90, x_4);
if (x_91 == 0)
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_ctor_get(x_9, 0);
x_93 = lean_ctor_get_uint8(x_92, sizeof(void*)*1);
if (x_93 == 0)
{
lean_dec(x_50);
x_12 = x_93;
x_13 = x_10;
x_14 = x_11;
goto block_18;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_94 = l_Lake_MTime_checkUpToDate___at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(x_2, x_5, x_11);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_unbox(x_95);
lean_dec(x_95);
x_51 = x_97;
x_52 = x_10;
x_53 = x_96;
goto block_88;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_98 = l_System_FilePath_pathExists(x_2, x_11);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_unbox(x_99);
lean_dec(x_99);
x_51 = x_101;
x_52 = x_10;
x_53 = x_100;
goto block_88;
}
block_88:
{
if (x_51 == 0)
{
lean_dec(x_50);
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
uint8_t x_55; lean_object* x_56; uint8_t x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_55 = lean_ctor_get_uint8(x_52, sizeof(void*)*2);
x_56 = lean_box(1);
x_57 = lean_unbox(x_56);
x_58 = l_Lake_JobAction_merge(x_55, x_57);
lean_ctor_set_uint8(x_52, sizeof(void*)*2, x_58);
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_array_get_size(x_50);
x_61 = lean_nat_dec_lt(x_59, x_60);
if (x_61 == 0)
{
lean_dec(x_60);
lean_dec(x_50);
x_19 = x_51;
x_20 = x_52;
x_21 = x_53;
goto block_25;
}
else
{
uint8_t x_62; 
x_62 = lean_nat_dec_le(x_60, x_60);
if (x_62 == 0)
{
lean_dec(x_60);
lean_dec(x_50);
x_19 = x_51;
x_20 = x_52;
x_21 = x_53;
goto block_25;
}
else
{
lean_object* x_63; size_t x_64; size_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_box(0);
x_64 = 0;
x_65 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_66 = l_Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___redArg(x_50, x_64, x_65, x_63, x_52, x_53);
lean_dec(x_50);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_19 = x_51;
x_20 = x_69;
x_21 = x_68;
goto block_25;
}
}
}
else
{
lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_70 = lean_ctor_get(x_52, 0);
x_71 = lean_ctor_get_uint8(x_52, sizeof(void*)*2);
x_72 = lean_ctor_get(x_52, 1);
lean_inc(x_72);
lean_inc(x_70);
lean_dec(x_52);
x_73 = lean_box(1);
x_74 = lean_unbox(x_73);
x_75 = l_Lake_JobAction_merge(x_71, x_74);
x_76 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_76, 0, x_70);
lean_ctor_set(x_76, 1, x_72);
lean_ctor_set_uint8(x_76, sizeof(void*)*2, x_75);
x_77 = lean_unsigned_to_nat(0u);
x_78 = lean_array_get_size(x_50);
x_79 = lean_nat_dec_lt(x_77, x_78);
if (x_79 == 0)
{
lean_dec(x_78);
lean_dec(x_50);
x_19 = x_51;
x_20 = x_76;
x_21 = x_53;
goto block_25;
}
else
{
uint8_t x_80; 
x_80 = lean_nat_dec_le(x_78, x_78);
if (x_80 == 0)
{
lean_dec(x_78);
lean_dec(x_50);
x_19 = x_51;
x_20 = x_76;
x_21 = x_53;
goto block_25;
}
else
{
lean_object* x_81; size_t x_82; size_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_81 = lean_box(0);
x_82 = 0;
x_83 = lean_usize_of_nat(x_78);
lean_dec(x_78);
x_84 = l_Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___redArg(x_50, x_82, x_83, x_81, x_76, x_53);
lean_dec(x_50);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_19 = x_51;
x_20 = x_87;
x_21 = x_86;
goto block_25;
}
}
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_102 = lean_ctor_get(x_4, 0);
lean_inc(x_102);
lean_dec(x_4);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 3);
lean_inc(x_104);
lean_dec(x_102);
x_128 = lean_ctor_get(x_3, 2);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_103);
lean_inc(x_128);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_128);
x_131 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__2(x_130, x_129);
if (x_131 == 0)
{
lean_object* x_132; uint8_t x_133; 
x_132 = lean_ctor_get(x_9, 0);
x_133 = lean_ctor_get_uint8(x_132, sizeof(void*)*1);
if (x_133 == 0)
{
lean_dec(x_104);
x_12 = x_133;
x_13 = x_10;
x_14 = x_11;
goto block_18;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_134 = l_Lake_MTime_checkUpToDate___at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(x_2, x_5, x_11);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_unbox(x_135);
lean_dec(x_135);
x_105 = x_137;
x_106 = x_10;
x_107 = x_136;
goto block_127;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_138 = l_System_FilePath_pathExists(x_2, x_11);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = lean_unbox(x_139);
lean_dec(x_139);
x_105 = x_141;
x_106 = x_10;
x_107 = x_140;
goto block_127;
}
block_127:
{
if (x_105 == 0)
{
lean_dec(x_104);
x_12 = x_105;
x_13 = x_106;
x_14 = x_107;
goto block_18;
}
else
{
lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
x_109 = lean_ctor_get_uint8(x_106, sizeof(void*)*2);
x_110 = lean_ctor_get(x_106, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_111 = x_106;
} else {
 lean_dec_ref(x_106);
 x_111 = lean_box(0);
}
x_112 = lean_box(1);
x_113 = lean_unbox(x_112);
x_114 = l_Lake_JobAction_merge(x_109, x_113);
if (lean_is_scalar(x_111)) {
 x_115 = lean_alloc_ctor(0, 2, 1);
} else {
 x_115 = x_111;
}
lean_ctor_set(x_115, 0, x_108);
lean_ctor_set(x_115, 1, x_110);
lean_ctor_set_uint8(x_115, sizeof(void*)*2, x_114);
x_116 = lean_unsigned_to_nat(0u);
x_117 = lean_array_get_size(x_104);
x_118 = lean_nat_dec_lt(x_116, x_117);
if (x_118 == 0)
{
lean_dec(x_117);
lean_dec(x_104);
x_19 = x_105;
x_20 = x_115;
x_21 = x_107;
goto block_25;
}
else
{
uint8_t x_119; 
x_119 = lean_nat_dec_le(x_117, x_117);
if (x_119 == 0)
{
lean_dec(x_117);
lean_dec(x_104);
x_19 = x_105;
x_20 = x_115;
x_21 = x_107;
goto block_25;
}
else
{
lean_object* x_120; size_t x_121; size_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_120 = lean_box(0);
x_121 = 0;
x_122 = lean_usize_of_nat(x_117);
lean_dec(x_117);
x_123 = l_Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___redArg(x_104, x_121, x_122, x_120, x_115, x_107);
lean_dec(x_104);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_19 = x_105;
x_20 = x_126;
x_21 = x_125;
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
LEAN_EXPORT lean_object* l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_53; uint8_t x_54; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_11, sizeof(void*)*2);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
x_53 = lean_ctor_get(x_10, 0);
lean_inc(x_53);
x_54 = lean_ctor_get_uint8(x_53, sizeof(void*)*1 + 2);
lean_dec(x_53);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_11);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_11, 1);
lean_dec(x_56);
x_57 = lean_ctor_get(x_11, 0);
lean_dec(x_57);
x_58 = l_Lake_JobAction_merge(x_14, x_6);
lean_inc(x_13);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_58);
x_59 = lean_apply_7(x_1, x_3, x_7, x_8, x_9, x_10, x_11, x_12);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_60, 1);
x_63 = lean_ctor_get(x_60, 0);
lean_dec(x_63);
x_64 = lean_ctor_get(x_59, 1);
lean_inc(x_64);
lean_dec(x_59);
x_65 = lean_ctor_get(x_62, 0);
lean_inc(x_65);
x_66 = lean_ctor_get_uint8(x_62, sizeof(void*)*2);
x_67 = lean_ctor_get(x_62, 1);
lean_inc(x_67);
x_68 = l_Lake_clearFileHash(x_2, x_64);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_free_object(x_60);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_16 = x_69;
x_17 = x_62;
x_18 = x_65;
x_19 = x_66;
x_20 = x_67;
x_21 = x_70;
goto block_52;
}
else
{
uint8_t x_71; 
lean_dec(x_13);
lean_dec(x_4);
x_71 = !lean_is_exclusive(x_62);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_ctor_get(x_62, 1);
lean_dec(x_72);
x_73 = lean_ctor_get(x_62, 0);
lean_dec(x_73);
x_74 = !lean_is_exclusive(x_68);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; 
x_75 = lean_ctor_get(x_68, 0);
x_76 = lean_io_error_to_string(x_75);
x_77 = lean_box(3);
x_78 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_78, 0, x_76);
x_79 = lean_unbox(x_77);
lean_ctor_set_uint8(x_78, sizeof(void*)*1, x_79);
x_80 = lean_array_get_size(x_65);
x_81 = lean_array_push(x_65, x_78);
lean_ctor_set(x_62, 0, x_81);
lean_ctor_set_tag(x_60, 1);
lean_ctor_set(x_60, 0, x_80);
lean_ctor_set_tag(x_68, 0);
lean_ctor_set(x_68, 0, x_60);
return x_68;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_82 = lean_ctor_get(x_68, 0);
x_83 = lean_ctor_get(x_68, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_68);
x_84 = lean_io_error_to_string(x_82);
x_85 = lean_box(3);
x_86 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_86, 0, x_84);
x_87 = lean_unbox(x_85);
lean_ctor_set_uint8(x_86, sizeof(void*)*1, x_87);
x_88 = lean_array_get_size(x_65);
x_89 = lean_array_push(x_65, x_86);
lean_ctor_set(x_62, 0, x_89);
lean_ctor_set_tag(x_60, 1);
lean_ctor_set(x_60, 0, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_60);
lean_ctor_set(x_90, 1, x_83);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_62);
x_91 = lean_ctor_get(x_68, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_68, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_93 = x_68;
} else {
 lean_dec_ref(x_68);
 x_93 = lean_box(0);
}
x_94 = lean_io_error_to_string(x_91);
x_95 = lean_box(3);
x_96 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_96, 0, x_94);
x_97 = lean_unbox(x_95);
lean_ctor_set_uint8(x_96, sizeof(void*)*1, x_97);
x_98 = lean_array_get_size(x_65);
x_99 = lean_array_push(x_65, x_96);
x_100 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_67);
lean_ctor_set_uint8(x_100, sizeof(void*)*2, x_66);
lean_ctor_set_tag(x_60, 1);
lean_ctor_set(x_60, 1, x_100);
lean_ctor_set(x_60, 0, x_98);
if (lean_is_scalar(x_93)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_93;
 lean_ctor_set_tag(x_101, 0);
}
lean_ctor_set(x_101, 0, x_60);
lean_ctor_set(x_101, 1, x_92);
return x_101;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; 
x_102 = lean_ctor_get(x_60, 1);
lean_inc(x_102);
lean_dec(x_60);
x_103 = lean_ctor_get(x_59, 1);
lean_inc(x_103);
lean_dec(x_59);
x_104 = lean_ctor_get(x_102, 0);
lean_inc(x_104);
x_105 = lean_ctor_get_uint8(x_102, sizeof(void*)*2);
x_106 = lean_ctor_get(x_102, 1);
lean_inc(x_106);
x_107 = l_Lake_clearFileHash(x_2, x_103);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_16 = x_108;
x_17 = x_102;
x_18 = x_104;
x_19 = x_105;
x_20 = x_106;
x_21 = x_109;
goto block_52;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_13);
lean_dec(x_4);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_110 = x_102;
} else {
 lean_dec_ref(x_102);
 x_110 = lean_box(0);
}
x_111 = lean_ctor_get(x_107, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_107, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_113 = x_107;
} else {
 lean_dec_ref(x_107);
 x_113 = lean_box(0);
}
x_114 = lean_io_error_to_string(x_111);
x_115 = lean_box(3);
x_116 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_116, 0, x_114);
x_117 = lean_unbox(x_115);
lean_ctor_set_uint8(x_116, sizeof(void*)*1, x_117);
x_118 = lean_array_get_size(x_104);
x_119 = lean_array_push(x_104, x_116);
if (lean_is_scalar(x_110)) {
 x_120 = lean_alloc_ctor(0, 2, 1);
} else {
 x_120 = x_110;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_106);
lean_ctor_set_uint8(x_120, sizeof(void*)*2, x_105);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_120);
if (lean_is_scalar(x_113)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_113;
 lean_ctor_set_tag(x_122, 0);
}
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_112);
return x_122;
}
}
}
else
{
lean_object* x_123; 
lean_dec(x_60);
lean_dec(x_2);
x_123 = lean_ctor_get(x_59, 0);
lean_inc(x_123);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; 
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
x_125 = lean_ctor_get(x_59, 1);
lean_inc(x_125);
lean_dec(x_59);
x_126 = lean_ctor_get(x_123, 0);
lean_inc(x_126);
lean_dec(x_123);
x_127 = lean_ctor_get(x_124, 0);
lean_inc(x_127);
x_128 = lean_ctor_get_uint8(x_124, sizeof(void*)*2);
x_129 = lean_ctor_get(x_124, 1);
lean_inc(x_129);
x_16 = x_126;
x_17 = x_124;
x_18 = x_127;
x_19 = x_128;
x_20 = x_129;
x_21 = x_125;
goto block_52;
}
else
{
lean_dec(x_123);
lean_dec(x_13);
lean_dec(x_4);
return x_59;
}
}
}
else
{
uint8_t x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_11);
x_130 = l_Lake_JobAction_merge(x_14, x_6);
lean_inc(x_13);
x_131 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_131, 0, x_13);
lean_ctor_set(x_131, 1, x_15);
lean_ctor_set_uint8(x_131, sizeof(void*)*2, x_130);
x_132 = lean_apply_7(x_1, x_3, x_7, x_8, x_9, x_10, x_131, x_12);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; 
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_135 = x_133;
} else {
 lean_dec_ref(x_133);
 x_135 = lean_box(0);
}
x_136 = lean_ctor_get(x_132, 1);
lean_inc(x_136);
lean_dec(x_132);
x_137 = lean_ctor_get(x_134, 0);
lean_inc(x_137);
x_138 = lean_ctor_get_uint8(x_134, sizeof(void*)*2);
x_139 = lean_ctor_get(x_134, 1);
lean_inc(x_139);
x_140 = l_Lake_clearFileHash(x_2, x_136);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_135);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_16 = x_141;
x_17 = x_134;
x_18 = x_137;
x_19 = x_138;
x_20 = x_139;
x_21 = x_142;
goto block_52;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_13);
lean_dec(x_4);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_143 = x_134;
} else {
 lean_dec_ref(x_134);
 x_143 = lean_box(0);
}
x_144 = lean_ctor_get(x_140, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_140, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_146 = x_140;
} else {
 lean_dec_ref(x_140);
 x_146 = lean_box(0);
}
x_147 = lean_io_error_to_string(x_144);
x_148 = lean_box(3);
x_149 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_149, 0, x_147);
x_150 = lean_unbox(x_148);
lean_ctor_set_uint8(x_149, sizeof(void*)*1, x_150);
x_151 = lean_array_get_size(x_137);
x_152 = lean_array_push(x_137, x_149);
if (lean_is_scalar(x_143)) {
 x_153 = lean_alloc_ctor(0, 2, 1);
} else {
 x_153 = x_143;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_139);
lean_ctor_set_uint8(x_153, sizeof(void*)*2, x_138);
if (lean_is_scalar(x_135)) {
 x_154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_154 = x_135;
 lean_ctor_set_tag(x_154, 1);
}
lean_ctor_set(x_154, 0, x_151);
lean_ctor_set(x_154, 1, x_153);
if (lean_is_scalar(x_146)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_146;
 lean_ctor_set_tag(x_155, 0);
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_145);
return x_155;
}
}
else
{
lean_object* x_156; 
lean_dec(x_133);
lean_dec(x_2);
x_156 = lean_ctor_get(x_132, 0);
lean_inc(x_156);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; 
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
x_158 = lean_ctor_get(x_132, 1);
lean_inc(x_158);
lean_dec(x_132);
x_159 = lean_ctor_get(x_156, 0);
lean_inc(x_159);
lean_dec(x_156);
x_160 = lean_ctor_get(x_157, 0);
lean_inc(x_160);
x_161 = lean_ctor_get_uint8(x_157, sizeof(void*)*2);
x_162 = lean_ctor_get(x_157, 1);
lean_inc(x_162);
x_16 = x_159;
x_17 = x_157;
x_18 = x_160;
x_19 = x_161;
x_20 = x_162;
x_21 = x_158;
goto block_52;
}
else
{
lean_dec(x_156);
lean_dec(x_13);
lean_dec(x_4);
return x_132;
}
}
}
}
else
{
uint8_t x_163; lean_object* x_164; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_163 = l_Lake_buildAction___redArg___closed__0;
x_164 = lean_io_exit(x_163, x_12);
if (lean_obj_tag(x_164) == 0)
{
uint8_t x_165; 
lean_dec(x_15);
lean_dec(x_13);
x_165 = !lean_is_exclusive(x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_164, 0);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_11);
lean_ctor_set(x_164, 0, x_167);
return x_164;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_168 = lean_ctor_get(x_164, 0);
x_169 = lean_ctor_get(x_164, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_164);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_11);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
}
else
{
uint8_t x_172; 
x_172 = !lean_is_exclusive(x_11);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_173 = lean_ctor_get(x_11, 1);
lean_dec(x_173);
x_174 = lean_ctor_get(x_11, 0);
lean_dec(x_174);
x_175 = !lean_is_exclusive(x_164);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_176 = lean_ctor_get(x_164, 0);
x_177 = lean_io_error_to_string(x_176);
x_178 = lean_box(3);
x_179 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_179, 0, x_177);
x_180 = lean_unbox(x_178);
lean_ctor_set_uint8(x_179, sizeof(void*)*1, x_180);
x_181 = lean_array_get_size(x_13);
x_182 = lean_array_push(x_13, x_179);
lean_ctor_set(x_11, 0, x_182);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_11);
lean_ctor_set_tag(x_164, 0);
lean_ctor_set(x_164, 0, x_183);
return x_164;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_184 = lean_ctor_get(x_164, 0);
x_185 = lean_ctor_get(x_164, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_164);
x_186 = lean_io_error_to_string(x_184);
x_187 = lean_box(3);
x_188 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_188, 0, x_186);
x_189 = lean_unbox(x_187);
lean_ctor_set_uint8(x_188, sizeof(void*)*1, x_189);
x_190 = lean_array_get_size(x_13);
x_191 = lean_array_push(x_13, x_188);
lean_ctor_set(x_11, 0, x_191);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_11);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_185);
return x_193;
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_11);
x_194 = lean_ctor_get(x_164, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_164, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_196 = x_164;
} else {
 lean_dec_ref(x_164);
 x_196 = lean_box(0);
}
x_197 = lean_io_error_to_string(x_194);
x_198 = lean_box(3);
x_199 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_199, 0, x_197);
x_200 = lean_unbox(x_198);
lean_ctor_set_uint8(x_199, sizeof(void*)*1, x_200);
x_201 = lean_array_get_size(x_13);
x_202 = lean_array_push(x_13, x_199);
x_203 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_15);
lean_ctor_set_uint8(x_203, sizeof(void*)*2, x_14);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_203);
if (lean_is_scalar(x_196)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_196;
 lean_ctor_set_tag(x_205, 0);
}
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_195);
return x_205;
}
}
}
block_52:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_array_get_size(x_13);
lean_dec(x_13);
x_23 = lean_array_get_size(x_18);
lean_inc(x_23);
x_24 = l_Array_extract___redArg(x_18, x_22, x_23);
x_25 = lean_box(0);
x_26 = l_Lake_writeTraceFile_go(x_5, x_4, x_25, x_24, x_21);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_18);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_16);
lean_ctor_set(x_29, 1, x_17);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_16);
lean_ctor_set(x_31, 1, x_17);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_17);
lean_dec(x_16);
x_33 = !lean_is_exclusive(x_26);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_26, 0);
x_35 = lean_io_error_to_string(x_34);
x_36 = lean_box(3);
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_35);
x_38 = lean_unbox(x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_38);
x_39 = lean_array_push(x_18, x_37);
x_40 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_20);
lean_ctor_set_uint8(x_40, sizeof(void*)*2, x_19);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_23);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set_tag(x_26, 0);
lean_ctor_set(x_26, 0, x_41);
return x_26;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_42 = lean_ctor_get(x_26, 0);
x_43 = lean_ctor_get(x_26, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_26);
x_44 = lean_io_error_to_string(x_42);
x_45 = lean_box(3);
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_44);
x_47 = lean_unbox(x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_47);
x_48 = lean_array_push(x_18, x_46);
x_49 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_20);
lean_ctor_set_uint8(x_49, sizeof(void*)*2, x_19);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_23);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_43);
return x_51;
}
}
}
}
}
static lean_object* _init_l_Lake_buildFileUnlessUpToDate_x27___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".trace", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_64; uint8_t x_69; 
x_69 = !lean_is_exclusive(x_9);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_70 = lean_ctor_get(x_9, 0);
x_71 = lean_ctor_get(x_9, 1);
x_72 = l_Lake_buildFileUnlessUpToDate_x27___closed__0;
lean_inc(x_1);
x_73 = lean_string_append(x_1, x_72);
lean_inc(x_73);
x_74 = l_Lake_readTraceFile(x_73, x_70, x_10);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
x_79 = lean_ctor_get(x_71, 3);
lean_inc(x_79);
lean_inc(x_71);
lean_ctor_set(x_9, 0, x_78);
x_80 = l_Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0(x_4, x_1, x_71, x_77, x_79, x_5, x_6, x_7, x_8, x_9, x_76);
lean_dec(x_79);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_unbox(x_82);
lean_dec(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; 
x_84 = lean_ctor_get(x_80, 1);
lean_inc(x_84);
lean_dec(x_80);
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
lean_dec(x_81);
x_86 = lean_box(3);
x_87 = lean_unbox(x_86);
lean_inc(x_8);
lean_inc(x_1);
x_88 = l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__4(x_2, x_1, x_4, x_71, x_73, x_87, x_5, x_6, x_7, x_8, x_85, x_84);
lean_dec(x_73);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_17 = x_91;
x_18 = x_90;
goto block_63;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_8);
lean_dec(x_1);
x_92 = lean_ctor_get(x_88, 1);
lean_inc(x_92);
lean_dec(x_88);
x_93 = lean_ctor_get(x_89, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_89, 1);
lean_inc(x_94);
lean_dec(x_89);
x_11 = x_93;
x_12 = x_94;
x_13 = x_92;
goto block_16;
}
}
else
{
lean_dec(x_81);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_64 = x_80;
goto block_68;
}
}
else
{
lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_95 = lean_ctor_get(x_9, 0);
x_96 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
x_97 = lean_ctor_get(x_9, 1);
lean_inc(x_97);
lean_inc(x_95);
lean_dec(x_9);
x_98 = l_Lake_buildFileUnlessUpToDate_x27___closed__0;
lean_inc(x_1);
x_99 = lean_string_append(x_1, x_98);
lean_inc(x_99);
x_100 = l_Lake_readTraceFile(x_99, x_95, x_10);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_dec(x_101);
x_105 = lean_ctor_get(x_97, 3);
lean_inc(x_105);
lean_inc(x_97);
x_106 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_97);
lean_ctor_set_uint8(x_106, sizeof(void*)*2, x_96);
x_107 = l_Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0(x_4, x_1, x_97, x_103, x_105, x_5, x_6, x_7, x_8, x_106, x_102);
lean_dec(x_105);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_unbox(x_109);
lean_dec(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; 
x_111 = lean_ctor_get(x_107, 1);
lean_inc(x_111);
lean_dec(x_107);
x_112 = lean_ctor_get(x_108, 1);
lean_inc(x_112);
lean_dec(x_108);
x_113 = lean_box(3);
x_114 = lean_unbox(x_113);
lean_inc(x_8);
lean_inc(x_1);
x_115 = l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__4(x_2, x_1, x_4, x_97, x_99, x_114, x_5, x_6, x_7, x_8, x_112, x_111);
lean_dec(x_99);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_17 = x_118;
x_18 = x_117;
goto block_63;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_8);
lean_dec(x_1);
x_119 = lean_ctor_get(x_115, 1);
lean_inc(x_119);
lean_dec(x_115);
x_120 = lean_ctor_get(x_116, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_116, 1);
lean_inc(x_121);
lean_dec(x_116);
x_11 = x_120;
x_12 = x_121;
x_13 = x_119;
goto block_16;
}
}
else
{
lean_dec(x_108);
lean_dec(x_99);
lean_dec(x_97);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_64 = x_107;
goto block_68;
}
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
block_63:
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Lake_fetchFileTrace___redArg(x_1, x_3, x_8, x_17, x_18);
lean_dec(x_8);
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
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_21);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_21, 1);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_21, 1, x_25);
lean_ctor_set(x_20, 0, x_29);
return x_19;
}
else
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get_uint8(x_21, sizeof(void*)*2);
lean_inc(x_30);
lean_dec(x_21);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_25);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_31);
lean_ctor_set(x_20, 1, x_33);
lean_ctor_set(x_20, 0, x_32);
return x_19;
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_20, 0);
lean_inc(x_34);
lean_dec(x_20);
x_35 = lean_ctor_get(x_21, 0);
lean_inc(x_35);
x_36 = lean_ctor_get_uint8(x_21, sizeof(void*)*2);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_37 = x_21;
} else {
 lean_dec_ref(x_21);
 x_37 = lean_box(0);
}
x_38 = lean_box(0);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 1);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_34);
lean_ctor_set_uint8(x_39, sizeof(void*)*2, x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_19, 0, x_40);
return x_19;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_19, 1);
lean_inc(x_41);
lean_dec(x_19);
x_42 = lean_ctor_get(x_20, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_43 = x_20;
} else {
 lean_dec_ref(x_20);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_21, 0);
lean_inc(x_44);
x_45 = lean_ctor_get_uint8(x_21, sizeof(void*)*2);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_46 = x_21;
} else {
 lean_dec_ref(x_21);
 x_46 = lean_box(0);
}
x_47 = lean_box(0);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 1);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_42);
lean_ctor_set_uint8(x_48, sizeof(void*)*2, x_45);
if (lean_is_scalar(x_43)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_43;
}
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_41);
return x_50;
}
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_19);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_19, 0);
lean_dec(x_52);
x_53 = !lean_is_exclusive(x_20);
if (x_53 == 0)
{
return x_19;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_20, 0);
x_55 = lean_ctor_get(x_20, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_20);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_19, 0, x_56);
return x_19;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_19, 1);
lean_inc(x_57);
lean_dec(x_19);
x_58 = lean_ctor_get(x_20, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_20, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_60 = x_20;
} else {
 lean_dec_ref(x_20);
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
block_68:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_17 = x_67;
x_18 = x_66;
goto block_63;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_MTime_checkUpToDate___at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___redArg(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__2(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__4(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lake_buildFileUnlessUpToDate_x27(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 1);
lean_dec(x_13);
lean_ctor_set(x_10, 1, x_2);
x_14 = l_Lake_buildFileUnlessUpToDate_x27(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_15, 1);
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_14, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_ctor_set(x_15, 0, x_21);
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_ctor_set(x_15, 0, x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_dec(x_15);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_27 = x_14;
} else {
 lean_dec_ref(x_14);
 x_27 = lean_box(0);
}
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
if (lean_is_scalar(x_27)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_27;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_14);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_14, 0);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_15);
if (x_33 == 0)
{
return x_14;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_15, 0);
x_35 = lean_ctor_get(x_15, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_15);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_14, 0, x_36);
return x_14;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_14, 1);
lean_inc(x_37);
lean_dec(x_14);
x_38 = lean_ctor_get(x_15, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_15, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_40 = x_15;
} else {
 lean_dec_ref(x_15);
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
lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_10, 0);
x_44 = lean_ctor_get_uint8(x_10, sizeof(void*)*2);
lean_inc(x_43);
lean_dec(x_10);
x_45 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_2);
lean_ctor_set_uint8(x_45, sizeof(void*)*2, x_44);
x_46 = l_Lake_buildFileUnlessUpToDate_x27(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_45, x_11);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_51 = x_46;
} else {
 lean_dec_ref(x_46);
 x_51 = lean_box(0);
}
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
if (lean_is_scalar(x_49)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_49;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_48);
if (lean_is_scalar(x_51)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_51;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_50);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_56 = x_46;
} else {
 lean_dec_ref(x_46);
 x_56 = lean_box(0);
}
x_57 = lean_ctor_get(x_47, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_47, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_59 = x_47;
} else {
 lean_dec_ref(x_47);
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
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lake_buildFileUnlessUpToDate(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
if (x_4 == 0)
{
lean_object* x_6; 
x_6 = l_IO_FS_readBinFile(x_2, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_18; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_9 = x_6;
} else {
 lean_dec_ref(x_6);
 x_9 = lean_box(0);
}
x_10 = lean_byte_array_hash(x_7);
x_11 = l_Lake_Cache_artifactPath(x_1, x_10, x_3);
x_18 = l_Lake_createParentDirs(x_11, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_IO_FS_writeBinFile(x_11, x_7, x_19);
lean_dec(x_7);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
lean_inc(x_2);
x_22 = l_Lake_writeFileHash(x_2, x_10, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_io_metadata(x_11, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_12 = x_26;
x_13 = x_27;
goto block_17;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = l_Lake_platformTrace___closed__4;
x_12 = x_28;
x_13 = x_29;
goto block_17;
}
}
else
{
uint8_t x_30; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_22);
if (x_30 == 0)
{
return x_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_22, 0);
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_22);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_2);
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
uint8_t x_38; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_18);
if (x_38 == 0)
{
return x_18;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_18, 0);
x_40 = lean_ctor_get(x_18, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_18);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
block_17:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_box_uint64(x_10);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 2, x_13);
lean_ctor_set(x_15, 3, x_14);
if (lean_is_scalar(x_9)) {
 x_16 = lean_alloc_ctor(0, 2, 0);
} else {
 x_16 = x_9;
}
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
else
{
uint8_t x_42; 
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_6);
if (x_42 == 0)
{
return x_6;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_6, 0);
x_44 = lean_ctor_get(x_6, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_6);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; 
x_46 = l_IO_FS_readFile(x_2, x_5);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_61; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = l_String_crlfToLf(x_47);
lean_dec(x_47);
x_51 = 1723;
x_52 = lean_string_hash(x_50);
x_53 = lean_uint64_mix_hash(x_51, x_52);
x_54 = l_Lake_Cache_artifactPath(x_1, x_53, x_3);
x_61 = l_Lake_createParentDirs(x_54, x_48);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = l_IO_FS_writeFile(x_54, x_50, x_62);
lean_dec(x_50);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
lean_inc(x_2);
x_65 = l_Lake_writeFileHash(x_2, x_53, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_io_metadata(x_54, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_55 = x_69;
x_56 = x_70;
goto block_60;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_67, 1);
lean_inc(x_71);
lean_dec(x_67);
x_72 = l_Lake_platformTrace___closed__4;
x_55 = x_71;
x_56 = x_72;
goto block_60;
}
}
else
{
uint8_t x_73; 
lean_dec(x_54);
lean_dec(x_49);
lean_dec(x_2);
x_73 = !lean_is_exclusive(x_65);
if (x_73 == 0)
{
return x_65;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_65, 0);
x_75 = lean_ctor_get(x_65, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_65);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_54);
lean_dec(x_49);
lean_dec(x_2);
x_77 = !lean_is_exclusive(x_63);
if (x_77 == 0)
{
return x_63;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_63, 0);
x_79 = lean_ctor_get(x_63, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_63);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_54);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_2);
x_81 = !lean_is_exclusive(x_61);
if (x_81 == 0)
{
return x_61;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_61, 0);
x_83 = lean_ctor_get(x_61, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_61);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
block_60:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_box_uint64(x_53);
x_58 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_58, 0, x_54);
lean_ctor_set(x_58, 1, x_2);
lean_ctor_set(x_58, 2, x_56);
lean_ctor_set(x_58, 3, x_57);
if (lean_is_scalar(x_49)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_49;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_55);
return x_59;
}
}
else
{
uint8_t x_85; 
lean_dec(x_2);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_46);
if (x_85 == 0)
{
return x_46;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_46, 0);
x_87 = lean_ctor_get(x_46, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_46);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lake_Cache_saveArtifact(x_1, x_2, x_3, x_6, x_5);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 6);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_box(x_3);
x_7 = lean_alloc_closure((void*)(l_Lake_Cache_saveArtifact___boxed), 5, 4);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_2);
lean_closure_set(x_7, 3, x_6);
x_8 = lean_apply_2(x_4, lean_box(0), x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_closure((void*)(l_Lake_cacheArtifact___redArg___lam__0___boxed), 1, 0);
x_12 = lean_box(x_6);
x_13 = lean_alloc_closure((void*)(l_Lake_cacheArtifact___redArg___lam__1___boxed), 5, 4);
lean_closure_set(x_13, 0, x_4);
lean_closure_set(x_13, 1, x_5);
lean_closure_set(x_13, 2, x_12);
lean_closure_set(x_13, 3, x_2);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_11, x_1);
x_15 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_14, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_closure((void*)(l_Lake_cacheArtifact___redArg___lam__0___boxed), 1, 0);
x_13 = lean_box(x_7);
x_14 = lean_alloc_closure((void*)(l_Lake_cacheArtifact___redArg___lam__1___boxed), 5, 4);
lean_closure_set(x_14, 0, x_5);
lean_closure_set(x_14, 1, x_6);
lean_closure_set(x_14, 2, x_13);
lean_closure_set(x_14, 3, x_3);
x_15 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_12, x_2);
x_16 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_15, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_cacheArtifact___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lake_cacheArtifact___redArg___lam__1(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = l_Lake_cacheArtifact___redArg(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
lean_dec(x_7);
x_9 = l_Lake_cacheArtifact(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifactTrace(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_12; 
x_12 = lean_io_metadata(x_2, x_4);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_5 = x_14;
x_6 = x_15;
goto block_11;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = l_Lake_platformTrace___closed__4;
x_5 = x_16;
x_6 = x_17;
goto block_11;
}
block_11:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lake_platformTrace___closed__2;
x_8 = lean_box_uint64(x_3);
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
lean_ctor_set(x_9, 3, x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifactTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_6 = l_Lake_computeArtifactTrace(x_1, x_2, x_5, x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfExists___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_7 = lean_ctor_get(x_5, 3);
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
x_10 = l_Lake_JobAction_merge(x_6, x_9);
lean_ctor_set_uint8(x_2, sizeof(void*)*2, x_10);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get_size(x_7);
x_13 = lean_box(0);
x_14 = lean_nat_dec_lt(x_11, x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_12, x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_22 = l_Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___redArg(x_7, x_20, x_21, x_13, x_2, x_3);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
lean_inc(x_24);
lean_dec(x_2);
x_27 = lean_ctor_get(x_23, 3);
x_28 = lean_box(1);
x_29 = lean_unbox(x_28);
x_30 = l_Lake_JobAction_merge(x_25, x_29);
x_31 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_26);
lean_ctor_set_uint8(x_31, sizeof(void*)*2, x_30);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_array_get_size(x_27);
x_34 = lean_box(0);
x_35 = lean_nat_dec_lt(x_32, x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_31);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_3);
return x_37;
}
else
{
uint8_t x_38; 
x_38 = lean_nat_dec_le(x_33, x_33);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_33);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_31);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_3);
return x_40;
}
else
{
size_t x_41; size_t x_42; lean_object* x_43; 
x_41 = 0;
x_42 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_43 = l_Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___redArg(x_27, x_41, x_42, x_34, x_31, x_3);
return x_43;
}
}
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_2);
if (x_44 == 0)
{
uint8_t x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_46 = lean_box(2);
x_47 = lean_box(0);
x_48 = lean_unbox(x_46);
x_49 = l_Lake_JobAction_merge(x_45, x_48);
lean_ctor_set_uint8(x_2, sizeof(void*)*2, x_49);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_2);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_3);
return x_51;
}
else
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_52 = lean_ctor_get(x_2, 0);
x_53 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_54 = lean_ctor_get(x_2, 1);
lean_inc(x_54);
lean_inc(x_52);
lean_dec(x_2);
x_55 = lean_box(2);
x_56 = lean_box(0);
x_57 = lean_unbox(x_55);
x_58 = l_Lake_JobAction_merge(x_53, x_57);
x_59 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_59, 0, x_52);
lean_ctor_set(x_59, 1, x_54);
lean_ctor_set_uint8(x_59, sizeof(void*)*2, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_56);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_3);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfExists(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_SavedTrace_replayIfExists___redArg(x_1, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfExists___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_SavedTrace_replayIfExists___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfExists___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_SavedTrace_replayIfExists(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l_Lake_resolveArtifactsUsing_x3f___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("input '", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_resolveArtifactsUsing_x3f___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' found in package artifact cache, but output(s) were in an unexpected format", 77, 77);
return x_1;
}
}
static lean_object* _init_l_Lake_resolveArtifactsUsing_x3f___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' found in package artifact cache, but some output(s) were not", 62, 62);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifactsUsing_x3f___redArg(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; 
x_59 = lean_st_ref_take(x_5, x_12);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_60);
x_62 = lean_st_ref_set(x_5, x_60, x_61);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_ctor_get(x_11, 0);
lean_inc(x_64);
x_65 = lean_ctor_get_uint8(x_11, sizeof(void*)*2);
x_66 = lean_ctor_get(x_11, 1);
lean_inc(x_66);
x_67 = l_Lake_CacheMap_get_x3f(x_3, x_60);
lean_dec(x_60);
if (lean_obj_tag(x_67) == 0)
{
lean_dec(x_66);
lean_dec(x_64);
x_19 = x_6;
x_20 = x_7;
x_21 = x_8;
x_22 = x_9;
x_23 = x_10;
x_24 = x_11;
x_25 = x_63;
goto block_58;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec(x_67);
lean_inc(x_1);
x_69 = lean_apply_1(x_1, x_68);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
lean_dec(x_69);
x_70 = !lean_is_exclusive(x_11);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; 
x_71 = lean_ctor_get(x_11, 1);
lean_dec(x_71);
x_72 = lean_ctor_get(x_11, 0);
lean_dec(x_72);
x_73 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__0;
x_74 = lean_uint64_to_nat(x_3);
x_75 = l_Nat_reprFast(x_74);
x_76 = lean_unsigned_to_nat(7u);
x_77 = lean_unsigned_to_nat(0u);
x_78 = lean_string_utf8_byte_size(x_75);
lean_inc(x_75);
x_79 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_77);
lean_ctor_set(x_79, 2, x_78);
x_80 = l_Substring_nextn(x_79, x_76, x_77);
lean_dec(x_79);
x_81 = lean_string_utf8_extract(x_75, x_77, x_80);
lean_dec(x_80);
lean_dec(x_75);
x_82 = lean_string_append(x_73, x_81);
lean_dec(x_81);
x_83 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__1;
x_84 = lean_string_append(x_82, x_83);
x_85 = lean_box(2);
x_86 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_86, 0, x_84);
x_87 = lean_unbox(x_85);
lean_ctor_set_uint8(x_86, sizeof(void*)*1, x_87);
x_88 = lean_array_push(x_64, x_86);
lean_ctor_set(x_11, 0, x_88);
x_19 = x_6;
x_20 = x_7;
x_21 = x_8;
x_22 = x_9;
x_23 = x_10;
x_24 = x_11;
x_25 = x_63;
goto block_58;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_11);
x_89 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__0;
x_90 = lean_uint64_to_nat(x_3);
x_91 = l_Nat_reprFast(x_90);
x_92 = lean_unsigned_to_nat(7u);
x_93 = lean_unsigned_to_nat(0u);
x_94 = lean_string_utf8_byte_size(x_91);
lean_inc(x_91);
x_95 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_95, 0, x_91);
lean_ctor_set(x_95, 1, x_93);
lean_ctor_set(x_95, 2, x_94);
x_96 = l_Substring_nextn(x_95, x_92, x_93);
lean_dec(x_95);
x_97 = lean_string_utf8_extract(x_91, x_93, x_96);
lean_dec(x_96);
lean_dec(x_91);
x_98 = lean_string_append(x_89, x_97);
lean_dec(x_97);
x_99 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__1;
x_100 = lean_string_append(x_98, x_99);
x_101 = lean_box(2);
x_102 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_102, 0, x_100);
x_103 = lean_unbox(x_101);
lean_ctor_set_uint8(x_102, sizeof(void*)*1, x_103);
x_104 = lean_array_push(x_64, x_102);
x_105 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_66);
lean_ctor_set_uint8(x_105, sizeof(void*)*2, x_65);
x_19 = x_6;
x_20 = x_7;
x_21 = x_8;
x_22 = x_9;
x_23 = x_10;
x_24 = x_105;
x_25 = x_63;
goto block_58;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_4);
lean_dec(x_1);
x_106 = lean_ctor_get(x_69, 0);
lean_inc(x_106);
lean_dec(x_69);
x_107 = lean_apply_8(x_2, x_106, x_6, x_7, x_8, x_9, x_10, x_11, x_63);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
if (lean_obj_tag(x_109) == 0)
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_108);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_111 = lean_ctor_get(x_108, 1);
x_112 = lean_ctor_get(x_108, 0);
lean_dec(x_112);
x_113 = !lean_is_exclusive(x_107);
if (x_113 == 0)
{
lean_object* x_114; uint8_t x_115; 
x_114 = lean_ctor_get(x_107, 0);
lean_dec(x_114);
x_115 = !lean_is_exclusive(x_111);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; 
x_116 = lean_ctor_get(x_111, 0);
x_117 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__0;
x_118 = lean_uint64_to_nat(x_3);
x_119 = l_Nat_reprFast(x_118);
x_120 = lean_unsigned_to_nat(7u);
x_121 = lean_unsigned_to_nat(0u);
x_122 = lean_string_utf8_byte_size(x_119);
lean_inc(x_119);
x_123 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_123, 0, x_119);
lean_ctor_set(x_123, 1, x_121);
lean_ctor_set(x_123, 2, x_122);
x_124 = l_Substring_nextn(x_123, x_120, x_121);
lean_dec(x_123);
x_125 = lean_string_utf8_extract(x_119, x_121, x_124);
lean_dec(x_124);
lean_dec(x_119);
x_126 = lean_string_append(x_117, x_125);
lean_dec(x_125);
x_127 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__2;
x_128 = lean_string_append(x_126, x_127);
x_129 = lean_box(2);
x_130 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_130, 0, x_128);
x_131 = lean_unbox(x_129);
lean_ctor_set_uint8(x_130, sizeof(void*)*1, x_131);
x_132 = lean_array_push(x_116, x_130);
lean_ctor_set(x_111, 0, x_132);
return x_107;
}
else
{
lean_object* x_133; uint8_t x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; 
x_133 = lean_ctor_get(x_111, 0);
x_134 = lean_ctor_get_uint8(x_111, sizeof(void*)*2);
x_135 = lean_ctor_get(x_111, 1);
lean_inc(x_135);
lean_inc(x_133);
lean_dec(x_111);
x_136 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__0;
x_137 = lean_uint64_to_nat(x_3);
x_138 = l_Nat_reprFast(x_137);
x_139 = lean_unsigned_to_nat(7u);
x_140 = lean_unsigned_to_nat(0u);
x_141 = lean_string_utf8_byte_size(x_138);
lean_inc(x_138);
x_142 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_142, 0, x_138);
lean_ctor_set(x_142, 1, x_140);
lean_ctor_set(x_142, 2, x_141);
x_143 = l_Substring_nextn(x_142, x_139, x_140);
lean_dec(x_142);
x_144 = lean_string_utf8_extract(x_138, x_140, x_143);
lean_dec(x_143);
lean_dec(x_138);
x_145 = lean_string_append(x_136, x_144);
lean_dec(x_144);
x_146 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__2;
x_147 = lean_string_append(x_145, x_146);
x_148 = lean_box(2);
x_149 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_149, 0, x_147);
x_150 = lean_unbox(x_148);
lean_ctor_set_uint8(x_149, sizeof(void*)*1, x_150);
x_151 = lean_array_push(x_133, x_149);
x_152 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_135);
lean_ctor_set_uint8(x_152, sizeof(void*)*2, x_134);
lean_ctor_set(x_108, 1, x_152);
return x_107;
}
}
else
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_153 = lean_ctor_get(x_107, 1);
lean_inc(x_153);
lean_dec(x_107);
x_154 = lean_ctor_get(x_111, 0);
lean_inc(x_154);
x_155 = lean_ctor_get_uint8(x_111, sizeof(void*)*2);
x_156 = lean_ctor_get(x_111, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_157 = x_111;
} else {
 lean_dec_ref(x_111);
 x_157 = lean_box(0);
}
x_158 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__0;
x_159 = lean_uint64_to_nat(x_3);
x_160 = l_Nat_reprFast(x_159);
x_161 = lean_unsigned_to_nat(7u);
x_162 = lean_unsigned_to_nat(0u);
x_163 = lean_string_utf8_byte_size(x_160);
lean_inc(x_160);
x_164 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_164, 0, x_160);
lean_ctor_set(x_164, 1, x_162);
lean_ctor_set(x_164, 2, x_163);
x_165 = l_Substring_nextn(x_164, x_161, x_162);
lean_dec(x_164);
x_166 = lean_string_utf8_extract(x_160, x_162, x_165);
lean_dec(x_165);
lean_dec(x_160);
x_167 = lean_string_append(x_158, x_166);
lean_dec(x_166);
x_168 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__2;
x_169 = lean_string_append(x_167, x_168);
x_170 = lean_box(2);
x_171 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_171, 0, x_169);
x_172 = lean_unbox(x_170);
lean_ctor_set_uint8(x_171, sizeof(void*)*1, x_172);
x_173 = lean_array_push(x_154, x_171);
if (lean_is_scalar(x_157)) {
 x_174 = lean_alloc_ctor(0, 2, 1);
} else {
 x_174 = x_157;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_156);
lean_ctor_set_uint8(x_174, sizeof(void*)*2, x_155);
lean_ctor_set(x_108, 1, x_174);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_108);
lean_ctor_set(x_175, 1, x_153);
return x_175;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_176 = lean_ctor_get(x_108, 1);
lean_inc(x_176);
lean_dec(x_108);
x_177 = lean_ctor_get(x_107, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_178 = x_107;
} else {
 lean_dec_ref(x_107);
 x_178 = lean_box(0);
}
x_179 = lean_ctor_get(x_176, 0);
lean_inc(x_179);
x_180 = lean_ctor_get_uint8(x_176, sizeof(void*)*2);
x_181 = lean_ctor_get(x_176, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_182 = x_176;
} else {
 lean_dec_ref(x_176);
 x_182 = lean_box(0);
}
x_183 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__0;
x_184 = lean_uint64_to_nat(x_3);
x_185 = l_Nat_reprFast(x_184);
x_186 = lean_unsigned_to_nat(7u);
x_187 = lean_unsigned_to_nat(0u);
x_188 = lean_string_utf8_byte_size(x_185);
lean_inc(x_185);
x_189 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_189, 0, x_185);
lean_ctor_set(x_189, 1, x_187);
lean_ctor_set(x_189, 2, x_188);
x_190 = l_Substring_nextn(x_189, x_186, x_187);
lean_dec(x_189);
x_191 = lean_string_utf8_extract(x_185, x_187, x_190);
lean_dec(x_190);
lean_dec(x_185);
x_192 = lean_string_append(x_183, x_191);
lean_dec(x_191);
x_193 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__2;
x_194 = lean_string_append(x_192, x_193);
x_195 = lean_box(2);
x_196 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_196, 0, x_194);
x_197 = lean_unbox(x_195);
lean_ctor_set_uint8(x_196, sizeof(void*)*1, x_197);
x_198 = lean_array_push(x_179, x_196);
if (lean_is_scalar(x_182)) {
 x_199 = lean_alloc_ctor(0, 2, 1);
} else {
 x_199 = x_182;
}
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_181);
lean_ctor_set_uint8(x_199, sizeof(void*)*2, x_180);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_109);
lean_ctor_set(x_200, 1, x_199);
if (lean_is_scalar(x_178)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_178;
}
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_177);
return x_201;
}
}
else
{
lean_dec(x_109);
lean_dec(x_108);
return x_107;
}
}
else
{
lean_dec(x_108);
return x_107;
}
}
}
block_18:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
block_58:
{
if (lean_obj_tag(x_4) == 2)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_4, 0);
lean_inc(x_26);
lean_dec(x_4);
x_27 = lean_ctor_get(x_26, 2);
lean_inc(x_27);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_2);
lean_dec(x_1);
x_13 = x_24;
x_14 = x_25;
goto block_18;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
lean_inc(x_28);
x_29 = lean_apply_1(x_1, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_2);
x_13 = x_24;
x_14 = x_25;
goto block_18;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_apply_8(x_2, x_30, x_19, x_20, x_21, x_22, x_23, x_24, x_25);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_28);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_13 = x_35;
x_14 = x_34;
goto block_18;
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = !lean_is_exclusive(x_32);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_38 = lean_ctor_get(x_32, 0);
lean_dec(x_38);
x_39 = lean_st_ref_take(x_5, x_36);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lake_CacheMap_insertCore(x_3, x_28, x_40);
x_43 = lean_st_ref_set(x_5, x_42, x_41);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
lean_ctor_set(x_43, 0, x_32);
return x_43;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_32);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_48 = lean_ctor_get(x_32, 1);
lean_inc(x_48);
lean_dec(x_32);
x_49 = lean_st_ref_take(x_5, x_36);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lake_CacheMap_insertCore(x_3, x_28, x_50);
x_53 = lean_st_ref_set(x_5, x_52, x_51);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_33);
lean_ctor_set(x_56, 1, x_48);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
return x_57;
}
}
}
else
{
lean_dec(x_32);
lean_dec(x_28);
return x_31;
}
}
}
}
else
{
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_13 = x_24;
x_14 = x_25;
goto block_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifactsUsing_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint64_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lake_resolveArtifactsUsing_x3f___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifactsUsing_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint64_t x_13; lean_object* x_14; 
x_13 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_14 = l_Lake_resolveArtifactsUsing_x3f___redArg(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifactsUsing_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint64_t x_15; lean_object* x_16; 
x_15 = lean_unbox_uint64(x_5);
lean_dec(x_5);
x_16 = l_Lake_resolveArtifactsUsing_x3f(x_1, x_2, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonFileOutputHash___lam__0(uint64_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_uint64_to_nat(x_1);
x_3 = l_Lean_bignumToJson(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonFileOutputHash(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instToJsonFileOutputHash___lam__0___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonFileOutputHash___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lake_instToJsonFileOutputHash___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonFileOutputHash___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instToJsonFileOutputHash(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instFromJsonFileOutputHash___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_UInt64_fromJson_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instFromJsonFileOutputHash(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instFromJsonFileOutputHash___lam__0), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instFromJsonFileOutputHash___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instFromJsonFileOutputHash(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instResolveArtifactsFileOutputHashArtifactOfMonadLakeEnvOfMonadLiftTBaseIOOfMonad___redArg___lam__0(uint64_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 6);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box_uint64(x_1);
x_7 = lean_alloc_closure((void*)(l_Lake_Cache_getArtifact_x3f___boxed), 4, 3);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_6);
lean_closure_set(x_7, 2, x_2);
x_8 = lean_apply_2(x_3, lean_box(0), x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_instResolveArtifactsFileOutputHashArtifactOfMonadLakeEnvOfMonadLiftTBaseIOOfMonad___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint64_t x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_box_uint64(x_5);
x_7 = lean_alloc_closure((void*)(l_Lake_instResolveArtifactsFileOutputHashArtifactOfMonadLakeEnvOfMonadLiftTBaseIOOfMonad___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_2);
x_8 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_instResolveArtifactsFileOutputHashArtifactOfMonadLakeEnvOfMonadLiftTBaseIOOfMonad___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_alloc_closure((void*)(l_Lake_instResolveArtifactsFileOutputHashArtifactOfMonadLakeEnvOfMonadLiftTBaseIOOfMonad___redArg___lam__1___boxed), 5, 4);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_3);
lean_closure_set(x_6, 2, x_5);
lean_closure_set(x_6, 3, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_instResolveArtifactsFileOutputHashArtifactOfMonadLakeEnvOfMonadLiftTBaseIOOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_instResolveArtifactsFileOutputHashArtifactOfMonadLakeEnvOfMonadLiftTBaseIOOfMonad___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_instResolveArtifactsFileOutputHashArtifactOfMonadLakeEnvOfMonadLiftTBaseIOOfMonad___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_6 = l_Lake_instResolveArtifactsFileOutputHashArtifactOfMonadLakeEnvOfMonadLiftTBaseIOOfMonad___redArg___lam__0(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_instResolveArtifactsFileOutputHashArtifactOfMonadLakeEnvOfMonadLiftTBaseIOOfMonad___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint64_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint64(x_5);
lean_dec(x_5);
x_7 = l_Lake_instResolveArtifactsFileOutputHashArtifactOfMonadLakeEnvOfMonadLiftTBaseIOOfMonad___redArg___lam__1(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchLocalArtifact___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_6 = l_Lake_fetchFileHash___redArg(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_20; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_9 = x_6;
} else {
 lean_dec_ref(x_6);
 x_9 = lean_box(0);
}
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_12 = x_7;
} else {
 lean_dec_ref(x_7);
 x_12 = lean_box(0);
}
x_20 = lean_io_metadata(x_1, x_8);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_13 = x_22;
x_14 = x_11;
x_15 = x_23;
goto block_19;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = l_Lake_platformTrace___closed__4;
x_13 = x_24;
x_14 = x_11;
x_15 = x_25;
goto block_19;
}
block_19:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_1);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_1);
lean_ctor_set(x_16, 2, x_15);
lean_ctor_set(x_16, 3, x_10);
if (lean_is_scalar(x_12)) {
 x_17 = lean_alloc_ctor(0, 2, 0);
} else {
 x_17 = x_12;
}
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
if (lean_is_scalar(x_9)) {
 x_18 = lean_alloc_ctor(0, 2, 0);
} else {
 x_18 = x_9;
}
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
}
else
{
uint8_t x_26; 
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_6);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_6, 0);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_7);
if (x_28 == 0)
{
return x_6;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_7, 0);
x_30 = lean_ctor_get(x_7, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_7);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_6, 0, x_31);
return x_6;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_6, 1);
lean_inc(x_32);
lean_dec(x_6);
x_33 = lean_ctor_get(x_7, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_7, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_35 = x_7;
} else {
 lean_dec_ref(x_7);
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
LEAN_EXPORT lean_object* l_Lake_fetchLocalArtifact(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_fetchLocalArtifact___redArg(x_1, x_2, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchLocalArtifact___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lake_fetchLocalArtifact___redArg(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchLocalArtifact___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lake_fetchLocalArtifact(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*1 + 2);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get_uint8(x_12, sizeof(void*)*2);
x_19 = l_Lake_JobAction_merge(x_18, x_7);
lean_inc(x_17);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_19);
x_20 = lean_apply_7(x_1, x_4, x_8, x_9, x_10, x_11, x_12, x_13);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_110; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_23 = x_21;
} else {
 lean_dec_ref(x_21);
 x_23 = lean_box(0);
}
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
x_26 = lean_ctor_get_uint8(x_22, sizeof(void*)*2);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_2);
x_110 = l_Lake_clearFileHash(x_2, x_24);
if (lean_obj_tag(x_110) == 0)
{
if (x_3 == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
x_112 = l_Lake_computeBinFileHash(x_2, x_111);
lean_dec(x_2);
x_28 = x_112;
goto block_109;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
lean_dec(x_110);
x_114 = l_Lake_computeTextFileHash(x_2, x_113);
lean_dec(x_2);
x_28 = x_114;
goto block_109;
}
}
else
{
uint8_t x_115; 
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_2);
x_115 = !lean_is_exclusive(x_22);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_116 = lean_ctor_get(x_22, 1);
lean_dec(x_116);
x_117 = lean_ctor_get(x_22, 0);
lean_dec(x_117);
x_118 = !lean_is_exclusive(x_110);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_119 = lean_ctor_get(x_110, 0);
x_120 = lean_io_error_to_string(x_119);
x_121 = lean_box(3);
x_122 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_122, 0, x_120);
x_123 = lean_unbox(x_121);
lean_ctor_set_uint8(x_122, sizeof(void*)*1, x_123);
x_124 = lean_array_get_size(x_25);
x_125 = lean_array_push(x_25, x_122);
lean_ctor_set(x_22, 0, x_125);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_22);
lean_ctor_set_tag(x_110, 0);
lean_ctor_set(x_110, 0, x_126);
return x_110;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_127 = lean_ctor_get(x_110, 0);
x_128 = lean_ctor_get(x_110, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_110);
x_129 = lean_io_error_to_string(x_127);
x_130 = lean_box(3);
x_131 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_131, 0, x_129);
x_132 = lean_unbox(x_130);
lean_ctor_set_uint8(x_131, sizeof(void*)*1, x_132);
x_133 = lean_array_get_size(x_25);
x_134 = lean_array_push(x_25, x_131);
lean_ctor_set(x_22, 0, x_134);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_22);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_128);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_22);
x_137 = lean_ctor_get(x_110, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_110, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_139 = x_110;
} else {
 lean_dec_ref(x_110);
 x_139 = lean_box(0);
}
x_140 = lean_io_error_to_string(x_137);
x_141 = lean_box(3);
x_142 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_142, 0, x_140);
x_143 = lean_unbox(x_141);
lean_ctor_set_uint8(x_142, sizeof(void*)*1, x_143);
x_144 = lean_array_get_size(x_25);
x_145 = lean_array_push(x_25, x_142);
x_146 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_27);
lean_ctor_set_uint8(x_146, sizeof(void*)*2, x_26);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_146);
if (lean_is_scalar(x_139)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_139;
 lean_ctor_set_tag(x_148, 0);
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_138);
return x_148;
}
}
block_109:
{
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint64_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_array_get_size(x_17);
lean_dec(x_17);
x_32 = lean_array_get_size(x_25);
lean_inc(x_32);
x_33 = l_Array_extract___redArg(x_25, x_31, x_32);
x_34 = lean_unbox_uint64(x_29);
x_35 = lean_uint64_to_nat(x_34);
x_36 = l_Lean_bignumToJson(x_35);
x_37 = l_Lake_writeTraceFile_go(x_6, x_5, x_36, x_33, x_30);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_25);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
if (lean_is_scalar(x_23)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_23;
}
lean_ctor_set(x_40, 0, x_29);
lean_ctor_set(x_40, 1, x_22);
lean_ctor_set(x_37, 0, x_40);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
if (lean_is_scalar(x_23)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_23;
}
lean_ctor_set(x_42, 0, x_29);
lean_ctor_set(x_42, 1, x_22);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_29);
x_44 = !lean_is_exclusive(x_22);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_22, 1);
lean_dec(x_45);
x_46 = lean_ctor_get(x_22, 0);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_37);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_37, 0);
x_49 = lean_io_error_to_string(x_48);
x_50 = lean_box(3);
x_51 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_51, 0, x_49);
x_52 = lean_unbox(x_50);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_52);
x_53 = lean_array_push(x_25, x_51);
lean_ctor_set(x_22, 0, x_53);
if (lean_is_scalar(x_23)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_23;
 lean_ctor_set_tag(x_54, 1);
}
lean_ctor_set(x_54, 0, x_32);
lean_ctor_set(x_54, 1, x_22);
lean_ctor_set_tag(x_37, 0);
lean_ctor_set(x_37, 0, x_54);
return x_37;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_55 = lean_ctor_get(x_37, 0);
x_56 = lean_ctor_get(x_37, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_37);
x_57 = lean_io_error_to_string(x_55);
x_58 = lean_box(3);
x_59 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_59, 0, x_57);
x_60 = lean_unbox(x_58);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_60);
x_61 = lean_array_push(x_25, x_59);
lean_ctor_set(x_22, 0, x_61);
if (lean_is_scalar(x_23)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_23;
 lean_ctor_set_tag(x_62, 1);
}
lean_ctor_set(x_62, 0, x_32);
lean_ctor_set(x_62, 1, x_22);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_56);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_22);
x_64 = lean_ctor_get(x_37, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_37, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_66 = x_37;
} else {
 lean_dec_ref(x_37);
 x_66 = lean_box(0);
}
x_67 = lean_io_error_to_string(x_64);
x_68 = lean_box(3);
x_69 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_69, 0, x_67);
x_70 = lean_unbox(x_68);
lean_ctor_set_uint8(x_69, sizeof(void*)*1, x_70);
x_71 = lean_array_push(x_25, x_69);
x_72 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_27);
lean_ctor_set_uint8(x_72, sizeof(void*)*2, x_26);
if (lean_is_scalar(x_23)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_23;
 lean_ctor_set_tag(x_73, 1);
}
lean_ctor_set(x_73, 0, x_32);
lean_ctor_set(x_73, 1, x_72);
if (lean_is_scalar(x_66)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_66;
 lean_ctor_set_tag(x_74, 0);
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_65);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_17);
lean_dec(x_5);
x_75 = !lean_is_exclusive(x_22);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = lean_ctor_get(x_22, 1);
lean_dec(x_76);
x_77 = lean_ctor_get(x_22, 0);
lean_dec(x_77);
x_78 = !lean_is_exclusive(x_28);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_79 = lean_ctor_get(x_28, 0);
x_80 = lean_io_error_to_string(x_79);
x_81 = lean_box(3);
x_82 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_82, 0, x_80);
x_83 = lean_unbox(x_81);
lean_ctor_set_uint8(x_82, sizeof(void*)*1, x_83);
x_84 = lean_array_get_size(x_25);
x_85 = lean_array_push(x_25, x_82);
lean_ctor_set(x_22, 0, x_85);
if (lean_is_scalar(x_23)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_23;
 lean_ctor_set_tag(x_86, 1);
}
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_22);
lean_ctor_set_tag(x_28, 0);
lean_ctor_set(x_28, 0, x_86);
return x_28;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_87 = lean_ctor_get(x_28, 0);
x_88 = lean_ctor_get(x_28, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_28);
x_89 = lean_io_error_to_string(x_87);
x_90 = lean_box(3);
x_91 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_91, 0, x_89);
x_92 = lean_unbox(x_90);
lean_ctor_set_uint8(x_91, sizeof(void*)*1, x_92);
x_93 = lean_array_get_size(x_25);
x_94 = lean_array_push(x_25, x_91);
lean_ctor_set(x_22, 0, x_94);
if (lean_is_scalar(x_23)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_23;
 lean_ctor_set_tag(x_95, 1);
}
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_22);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_88);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_22);
x_97 = lean_ctor_get(x_28, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_28, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_99 = x_28;
} else {
 lean_dec_ref(x_28);
 x_99 = lean_box(0);
}
x_100 = lean_io_error_to_string(x_97);
x_101 = lean_box(3);
x_102 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_102, 0, x_100);
x_103 = lean_unbox(x_101);
lean_ctor_set_uint8(x_102, sizeof(void*)*1, x_103);
x_104 = lean_array_get_size(x_25);
x_105 = lean_array_push(x_25, x_102);
x_106 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_27);
lean_ctor_set_uint8(x_106, sizeof(void*)*2, x_26);
if (lean_is_scalar(x_23)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_23;
 lean_ctor_set_tag(x_107, 1);
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_106);
if (lean_is_scalar(x_99)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_99;
 lean_ctor_set_tag(x_108, 0);
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_98);
return x_108;
}
}
}
}
else
{
uint8_t x_149; 
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_2);
x_149 = !lean_is_exclusive(x_20);
if (x_149 == 0)
{
lean_object* x_150; uint8_t x_151; 
x_150 = lean_ctor_get(x_20, 0);
lean_dec(x_150);
x_151 = !lean_is_exclusive(x_21);
if (x_151 == 0)
{
return x_20;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_21, 0);
x_153 = lean_ctor_get(x_21, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_21);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
lean_ctor_set(x_20, 0, x_154);
return x_20;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_155 = lean_ctor_get(x_20, 1);
lean_inc(x_155);
lean_dec(x_20);
x_156 = lean_ctor_get(x_21, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_21, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_158 = x_21;
} else {
 lean_dec_ref(x_21);
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
}
else
{
lean_object* x_161; uint8_t x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_161 = lean_ctor_get(x_12, 0);
x_162 = lean_ctor_get_uint8(x_12, sizeof(void*)*2);
x_163 = lean_ctor_get(x_12, 1);
lean_inc(x_163);
lean_inc(x_161);
lean_dec(x_12);
x_164 = l_Lake_JobAction_merge(x_162, x_7);
lean_inc(x_161);
x_165 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_165, 0, x_161);
lean_ctor_set(x_165, 1, x_163);
lean_ctor_set_uint8(x_165, sizeof(void*)*2, x_164);
x_166 = lean_apply_7(x_1, x_4, x_8, x_9, x_10, x_11, x_165, x_13);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_214; 
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_169 = x_167;
} else {
 lean_dec_ref(x_167);
 x_169 = lean_box(0);
}
x_170 = lean_ctor_get(x_166, 1);
lean_inc(x_170);
lean_dec(x_166);
x_171 = lean_ctor_get(x_168, 0);
lean_inc(x_171);
x_172 = lean_ctor_get_uint8(x_168, sizeof(void*)*2);
x_173 = lean_ctor_get(x_168, 1);
lean_inc(x_173);
lean_inc(x_2);
x_214 = l_Lake_clearFileHash(x_2, x_170);
if (lean_obj_tag(x_214) == 0)
{
if (x_3 == 0)
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
lean_dec(x_214);
x_216 = l_Lake_computeBinFileHash(x_2, x_215);
lean_dec(x_2);
x_174 = x_216;
goto block_213;
}
else
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_ctor_get(x_214, 1);
lean_inc(x_217);
lean_dec(x_214);
x_218 = l_Lake_computeTextFileHash(x_2, x_217);
lean_dec(x_2);
x_174 = x_218;
goto block_213;
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_169);
lean_dec(x_161);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_219 = x_168;
} else {
 lean_dec_ref(x_168);
 x_219 = lean_box(0);
}
x_220 = lean_ctor_get(x_214, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_214, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_222 = x_214;
} else {
 lean_dec_ref(x_214);
 x_222 = lean_box(0);
}
x_223 = lean_io_error_to_string(x_220);
x_224 = lean_box(3);
x_225 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_225, 0, x_223);
x_226 = lean_unbox(x_224);
lean_ctor_set_uint8(x_225, sizeof(void*)*1, x_226);
x_227 = lean_array_get_size(x_171);
x_228 = lean_array_push(x_171, x_225);
if (lean_is_scalar(x_219)) {
 x_229 = lean_alloc_ctor(0, 2, 1);
} else {
 x_229 = x_219;
}
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_173);
lean_ctor_set_uint8(x_229, sizeof(void*)*2, x_172);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_227);
lean_ctor_set(x_230, 1, x_229);
if (lean_is_scalar(x_222)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_222;
 lean_ctor_set_tag(x_231, 0);
}
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_221);
return x_231;
}
block_213:
{
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint64_t x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec(x_174);
x_177 = lean_array_get_size(x_161);
lean_dec(x_161);
x_178 = lean_array_get_size(x_171);
lean_inc(x_178);
x_179 = l_Array_extract___redArg(x_171, x_177, x_178);
x_180 = lean_unbox_uint64(x_175);
x_181 = lean_uint64_to_nat(x_180);
x_182 = l_Lean_bignumToJson(x_181);
x_183 = l_Lake_writeTraceFile_go(x_6, x_5, x_182, x_179, x_176);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_178);
lean_dec(x_173);
lean_dec(x_171);
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_185 = x_183;
} else {
 lean_dec_ref(x_183);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_169;
}
lean_ctor_set(x_186, 0, x_175);
lean_ctor_set(x_186, 1, x_168);
if (lean_is_scalar(x_185)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_185;
}
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_184);
return x_187;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_175);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_188 = x_168;
} else {
 lean_dec_ref(x_168);
 x_188 = lean_box(0);
}
x_189 = lean_ctor_get(x_183, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_183, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_191 = x_183;
} else {
 lean_dec_ref(x_183);
 x_191 = lean_box(0);
}
x_192 = lean_io_error_to_string(x_189);
x_193 = lean_box(3);
x_194 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_194, 0, x_192);
x_195 = lean_unbox(x_193);
lean_ctor_set_uint8(x_194, sizeof(void*)*1, x_195);
x_196 = lean_array_push(x_171, x_194);
if (lean_is_scalar(x_188)) {
 x_197 = lean_alloc_ctor(0, 2, 1);
} else {
 x_197 = x_188;
}
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_173);
lean_ctor_set_uint8(x_197, sizeof(void*)*2, x_172);
if (lean_is_scalar(x_169)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_169;
 lean_ctor_set_tag(x_198, 1);
}
lean_ctor_set(x_198, 0, x_178);
lean_ctor_set(x_198, 1, x_197);
if (lean_is_scalar(x_191)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_191;
 lean_ctor_set_tag(x_199, 0);
}
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_190);
return x_199;
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_161);
lean_dec(x_5);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_200 = x_168;
} else {
 lean_dec_ref(x_168);
 x_200 = lean_box(0);
}
x_201 = lean_ctor_get(x_174, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_174, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_203 = x_174;
} else {
 lean_dec_ref(x_174);
 x_203 = lean_box(0);
}
x_204 = lean_io_error_to_string(x_201);
x_205 = lean_box(3);
x_206 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_206, 0, x_204);
x_207 = lean_unbox(x_205);
lean_ctor_set_uint8(x_206, sizeof(void*)*1, x_207);
x_208 = lean_array_get_size(x_171);
x_209 = lean_array_push(x_171, x_206);
if (lean_is_scalar(x_200)) {
 x_210 = lean_alloc_ctor(0, 2, 1);
} else {
 x_210 = x_200;
}
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_173);
lean_ctor_set_uint8(x_210, sizeof(void*)*2, x_172);
if (lean_is_scalar(x_169)) {
 x_211 = lean_alloc_ctor(1, 2, 0);
} else {
 x_211 = x_169;
 lean_ctor_set_tag(x_211, 1);
}
lean_ctor_set(x_211, 0, x_208);
lean_ctor_set(x_211, 1, x_210);
if (lean_is_scalar(x_203)) {
 x_212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_212 = x_203;
 lean_ctor_set_tag(x_212, 0);
}
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_202);
return x_212;
}
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_161);
lean_dec(x_5);
lean_dec(x_2);
x_232 = lean_ctor_get(x_166, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_233 = x_166;
} else {
 lean_dec_ref(x_166);
 x_233 = lean_box(0);
}
x_234 = lean_ctor_get(x_167, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_167, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_236 = x_167;
} else {
 lean_dec_ref(x_167);
 x_236 = lean_box(0);
}
if (lean_is_scalar(x_236)) {
 x_237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_237 = x_236;
}
lean_ctor_set(x_237, 0, x_234);
lean_ctor_set(x_237, 1, x_235);
if (lean_is_scalar(x_233)) {
 x_238 = lean_alloc_ctor(0, 2, 0);
} else {
 x_238 = x_233;
}
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_232);
return x_238;
}
}
}
else
{
lean_object* x_239; uint8_t x_240; lean_object* x_241; uint8_t x_242; lean_object* x_243; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_239 = lean_ctor_get(x_12, 0);
lean_inc(x_239);
x_240 = lean_ctor_get_uint8(x_12, sizeof(void*)*2);
x_241 = lean_ctor_get(x_12, 1);
lean_inc(x_241);
x_242 = l_Lake_buildAction___redArg___closed__0;
x_243 = lean_io_exit(x_242, x_13);
if (lean_obj_tag(x_243) == 0)
{
uint8_t x_244; 
lean_dec(x_241);
lean_dec(x_239);
x_244 = !lean_is_exclusive(x_243);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; 
x_245 = lean_ctor_get(x_243, 0);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_12);
lean_ctor_set(x_243, 0, x_246);
return x_243;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_247 = lean_ctor_get(x_243, 0);
x_248 = lean_ctor_get(x_243, 1);
lean_inc(x_248);
lean_inc(x_247);
lean_dec(x_243);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_12);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_248);
return x_250;
}
}
else
{
uint8_t x_251; 
x_251 = !lean_is_exclusive(x_12);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; uint8_t x_254; 
x_252 = lean_ctor_get(x_12, 1);
lean_dec(x_252);
x_253 = lean_ctor_get(x_12, 0);
lean_dec(x_253);
x_254 = !lean_is_exclusive(x_243);
if (x_254 == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_255 = lean_ctor_get(x_243, 0);
x_256 = lean_io_error_to_string(x_255);
x_257 = lean_box(3);
x_258 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_258, 0, x_256);
x_259 = lean_unbox(x_257);
lean_ctor_set_uint8(x_258, sizeof(void*)*1, x_259);
x_260 = lean_array_get_size(x_239);
x_261 = lean_array_push(x_239, x_258);
lean_ctor_set(x_12, 0, x_261);
x_262 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_12);
lean_ctor_set_tag(x_243, 0);
lean_ctor_set(x_243, 0, x_262);
return x_243;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_263 = lean_ctor_get(x_243, 0);
x_264 = lean_ctor_get(x_243, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_243);
x_265 = lean_io_error_to_string(x_263);
x_266 = lean_box(3);
x_267 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_267, 0, x_265);
x_268 = lean_unbox(x_266);
lean_ctor_set_uint8(x_267, sizeof(void*)*1, x_268);
x_269 = lean_array_get_size(x_239);
x_270 = lean_array_push(x_239, x_267);
lean_ctor_set(x_12, 0, x_270);
x_271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_12);
x_272 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_264);
return x_272;
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; uint8_t x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_12);
x_273 = lean_ctor_get(x_243, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_243, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_275 = x_243;
} else {
 lean_dec_ref(x_243);
 x_275 = lean_box(0);
}
x_276 = lean_io_error_to_string(x_273);
x_277 = lean_box(3);
x_278 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_278, 0, x_276);
x_279 = lean_unbox(x_277);
lean_ctor_set_uint8(x_278, sizeof(void*)*1, x_279);
x_280 = lean_array_get_size(x_239);
x_281 = lean_array_push(x_239, x_278);
x_282 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_241);
lean_ctor_set_uint8(x_282, sizeof(void*)*2, x_240);
x_283 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_283, 0, x_280);
lean_ctor_set(x_283, 1, x_282);
if (lean_is_scalar(x_275)) {
 x_284 = lean_alloc_ctor(0, 2, 0);
} else {
 x_284 = x_275;
 lean_ctor_set_tag(x_284, 0);
}
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_274);
return x_284;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate_doBuild(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_box(3);
x_14 = lean_unbox(x_13);
x_15 = l_Lake_buildAction___at___Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(x_2, x_1, x_3, x_6, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_7);
lean_dec(x_7);
x_16 = l_Lake_buildAction___at___Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(x_1, x_2, x_14, x_4, x_5, x_6, x_15, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate_doBuild___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifactsUsing_x3f___at___Lake_buildArtifactUnlessUpToDate_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint64_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; 
x_59 = lean_st_ref_take(x_6, x_12);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_60);
x_62 = lean_st_ref_set(x_6, x_60, x_61);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_ctor_get(x_11, 0);
lean_inc(x_64);
x_65 = lean_ctor_get_uint8(x_11, sizeof(void*)*2);
x_66 = lean_ctor_get(x_11, 1);
lean_inc(x_66);
x_67 = l_Lake_CacheMap_get_x3f(x_4, x_60);
lean_dec(x_60);
if (lean_obj_tag(x_67) == 0)
{
lean_dec(x_66);
lean_dec(x_64);
x_19 = x_3;
x_20 = x_7;
x_21 = x_8;
x_22 = x_9;
x_23 = x_10;
x_24 = x_11;
x_25 = x_63;
goto block_58;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec(x_67);
lean_inc(x_1);
x_69 = lean_apply_1(x_1, x_68);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
lean_dec(x_69);
x_70 = !lean_is_exclusive(x_11);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; 
x_71 = lean_ctor_get(x_11, 1);
lean_dec(x_71);
x_72 = lean_ctor_get(x_11, 0);
lean_dec(x_72);
x_73 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__0;
x_74 = lean_uint64_to_nat(x_4);
x_75 = l_Nat_reprFast(x_74);
x_76 = lean_unsigned_to_nat(7u);
x_77 = lean_unsigned_to_nat(0u);
x_78 = lean_string_utf8_byte_size(x_75);
lean_inc(x_75);
x_79 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_77);
lean_ctor_set(x_79, 2, x_78);
x_80 = l_Substring_nextn(x_79, x_76, x_77);
lean_dec(x_79);
x_81 = lean_string_utf8_extract(x_75, x_77, x_80);
lean_dec(x_80);
lean_dec(x_75);
x_82 = lean_string_append(x_73, x_81);
lean_dec(x_81);
x_83 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__1;
x_84 = lean_string_append(x_82, x_83);
x_85 = lean_box(2);
x_86 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_86, 0, x_84);
x_87 = lean_unbox(x_85);
lean_ctor_set_uint8(x_86, sizeof(void*)*1, x_87);
x_88 = lean_array_push(x_64, x_86);
lean_ctor_set(x_11, 0, x_88);
x_19 = x_3;
x_20 = x_7;
x_21 = x_8;
x_22 = x_9;
x_23 = x_10;
x_24 = x_11;
x_25 = x_63;
goto block_58;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_11);
x_89 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__0;
x_90 = lean_uint64_to_nat(x_4);
x_91 = l_Nat_reprFast(x_90);
x_92 = lean_unsigned_to_nat(7u);
x_93 = lean_unsigned_to_nat(0u);
x_94 = lean_string_utf8_byte_size(x_91);
lean_inc(x_91);
x_95 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_95, 0, x_91);
lean_ctor_set(x_95, 1, x_93);
lean_ctor_set(x_95, 2, x_94);
x_96 = l_Substring_nextn(x_95, x_92, x_93);
lean_dec(x_95);
x_97 = lean_string_utf8_extract(x_91, x_93, x_96);
lean_dec(x_96);
lean_dec(x_91);
x_98 = lean_string_append(x_89, x_97);
lean_dec(x_97);
x_99 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__1;
x_100 = lean_string_append(x_98, x_99);
x_101 = lean_box(2);
x_102 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_102, 0, x_100);
x_103 = lean_unbox(x_101);
lean_ctor_set_uint8(x_102, sizeof(void*)*1, x_103);
x_104 = lean_array_push(x_64, x_102);
x_105 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_66);
lean_ctor_set_uint8(x_105, sizeof(void*)*2, x_65);
x_19 = x_3;
x_20 = x_7;
x_21 = x_8;
x_22 = x_9;
x_23 = x_10;
x_24 = x_105;
x_25 = x_63;
goto block_58;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_5);
lean_dec(x_1);
x_106 = lean_ctor_get(x_69, 0);
lean_inc(x_106);
lean_dec(x_69);
x_107 = lean_apply_8(x_2, x_106, x_3, x_7, x_8, x_9, x_10, x_11, x_63);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
if (lean_obj_tag(x_109) == 0)
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_108);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_111 = lean_ctor_get(x_108, 1);
x_112 = lean_ctor_get(x_108, 0);
lean_dec(x_112);
x_113 = !lean_is_exclusive(x_107);
if (x_113 == 0)
{
lean_object* x_114; uint8_t x_115; 
x_114 = lean_ctor_get(x_107, 0);
lean_dec(x_114);
x_115 = !lean_is_exclusive(x_111);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; 
x_116 = lean_ctor_get(x_111, 0);
x_117 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__0;
x_118 = lean_uint64_to_nat(x_4);
x_119 = l_Nat_reprFast(x_118);
x_120 = lean_unsigned_to_nat(7u);
x_121 = lean_unsigned_to_nat(0u);
x_122 = lean_string_utf8_byte_size(x_119);
lean_inc(x_119);
x_123 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_123, 0, x_119);
lean_ctor_set(x_123, 1, x_121);
lean_ctor_set(x_123, 2, x_122);
x_124 = l_Substring_nextn(x_123, x_120, x_121);
lean_dec(x_123);
x_125 = lean_string_utf8_extract(x_119, x_121, x_124);
lean_dec(x_124);
lean_dec(x_119);
x_126 = lean_string_append(x_117, x_125);
lean_dec(x_125);
x_127 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__2;
x_128 = lean_string_append(x_126, x_127);
x_129 = lean_box(2);
x_130 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_130, 0, x_128);
x_131 = lean_unbox(x_129);
lean_ctor_set_uint8(x_130, sizeof(void*)*1, x_131);
x_132 = lean_array_push(x_116, x_130);
lean_ctor_set(x_111, 0, x_132);
return x_107;
}
else
{
lean_object* x_133; uint8_t x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; 
x_133 = lean_ctor_get(x_111, 0);
x_134 = lean_ctor_get_uint8(x_111, sizeof(void*)*2);
x_135 = lean_ctor_get(x_111, 1);
lean_inc(x_135);
lean_inc(x_133);
lean_dec(x_111);
x_136 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__0;
x_137 = lean_uint64_to_nat(x_4);
x_138 = l_Nat_reprFast(x_137);
x_139 = lean_unsigned_to_nat(7u);
x_140 = lean_unsigned_to_nat(0u);
x_141 = lean_string_utf8_byte_size(x_138);
lean_inc(x_138);
x_142 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_142, 0, x_138);
lean_ctor_set(x_142, 1, x_140);
lean_ctor_set(x_142, 2, x_141);
x_143 = l_Substring_nextn(x_142, x_139, x_140);
lean_dec(x_142);
x_144 = lean_string_utf8_extract(x_138, x_140, x_143);
lean_dec(x_143);
lean_dec(x_138);
x_145 = lean_string_append(x_136, x_144);
lean_dec(x_144);
x_146 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__2;
x_147 = lean_string_append(x_145, x_146);
x_148 = lean_box(2);
x_149 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_149, 0, x_147);
x_150 = lean_unbox(x_148);
lean_ctor_set_uint8(x_149, sizeof(void*)*1, x_150);
x_151 = lean_array_push(x_133, x_149);
x_152 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_135);
lean_ctor_set_uint8(x_152, sizeof(void*)*2, x_134);
lean_ctor_set(x_108, 1, x_152);
return x_107;
}
}
else
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_153 = lean_ctor_get(x_107, 1);
lean_inc(x_153);
lean_dec(x_107);
x_154 = lean_ctor_get(x_111, 0);
lean_inc(x_154);
x_155 = lean_ctor_get_uint8(x_111, sizeof(void*)*2);
x_156 = lean_ctor_get(x_111, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_157 = x_111;
} else {
 lean_dec_ref(x_111);
 x_157 = lean_box(0);
}
x_158 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__0;
x_159 = lean_uint64_to_nat(x_4);
x_160 = l_Nat_reprFast(x_159);
x_161 = lean_unsigned_to_nat(7u);
x_162 = lean_unsigned_to_nat(0u);
x_163 = lean_string_utf8_byte_size(x_160);
lean_inc(x_160);
x_164 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_164, 0, x_160);
lean_ctor_set(x_164, 1, x_162);
lean_ctor_set(x_164, 2, x_163);
x_165 = l_Substring_nextn(x_164, x_161, x_162);
lean_dec(x_164);
x_166 = lean_string_utf8_extract(x_160, x_162, x_165);
lean_dec(x_165);
lean_dec(x_160);
x_167 = lean_string_append(x_158, x_166);
lean_dec(x_166);
x_168 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__2;
x_169 = lean_string_append(x_167, x_168);
x_170 = lean_box(2);
x_171 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_171, 0, x_169);
x_172 = lean_unbox(x_170);
lean_ctor_set_uint8(x_171, sizeof(void*)*1, x_172);
x_173 = lean_array_push(x_154, x_171);
if (lean_is_scalar(x_157)) {
 x_174 = lean_alloc_ctor(0, 2, 1);
} else {
 x_174 = x_157;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_156);
lean_ctor_set_uint8(x_174, sizeof(void*)*2, x_155);
lean_ctor_set(x_108, 1, x_174);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_108);
lean_ctor_set(x_175, 1, x_153);
return x_175;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_176 = lean_ctor_get(x_108, 1);
lean_inc(x_176);
lean_dec(x_108);
x_177 = lean_ctor_get(x_107, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_178 = x_107;
} else {
 lean_dec_ref(x_107);
 x_178 = lean_box(0);
}
x_179 = lean_ctor_get(x_176, 0);
lean_inc(x_179);
x_180 = lean_ctor_get_uint8(x_176, sizeof(void*)*2);
x_181 = lean_ctor_get(x_176, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_182 = x_176;
} else {
 lean_dec_ref(x_176);
 x_182 = lean_box(0);
}
x_183 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__0;
x_184 = lean_uint64_to_nat(x_4);
x_185 = l_Nat_reprFast(x_184);
x_186 = lean_unsigned_to_nat(7u);
x_187 = lean_unsigned_to_nat(0u);
x_188 = lean_string_utf8_byte_size(x_185);
lean_inc(x_185);
x_189 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_189, 0, x_185);
lean_ctor_set(x_189, 1, x_187);
lean_ctor_set(x_189, 2, x_188);
x_190 = l_Substring_nextn(x_189, x_186, x_187);
lean_dec(x_189);
x_191 = lean_string_utf8_extract(x_185, x_187, x_190);
lean_dec(x_190);
lean_dec(x_185);
x_192 = lean_string_append(x_183, x_191);
lean_dec(x_191);
x_193 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__2;
x_194 = lean_string_append(x_192, x_193);
x_195 = lean_box(2);
x_196 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_196, 0, x_194);
x_197 = lean_unbox(x_195);
lean_ctor_set_uint8(x_196, sizeof(void*)*1, x_197);
x_198 = lean_array_push(x_179, x_196);
if (lean_is_scalar(x_182)) {
 x_199 = lean_alloc_ctor(0, 2, 1);
} else {
 x_199 = x_182;
}
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_181);
lean_ctor_set_uint8(x_199, sizeof(void*)*2, x_180);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_109);
lean_ctor_set(x_200, 1, x_199);
if (lean_is_scalar(x_178)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_178;
}
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_177);
return x_201;
}
}
else
{
lean_dec(x_109);
lean_dec(x_108);
return x_107;
}
}
else
{
lean_dec(x_108);
return x_107;
}
}
}
block_18:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
block_58:
{
if (lean_obj_tag(x_5) == 2)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_5, 0);
lean_inc(x_26);
lean_dec(x_5);
x_27 = lean_ctor_get(x_26, 2);
lean_inc(x_27);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_2);
lean_dec(x_1);
x_13 = x_24;
x_14 = x_25;
goto block_18;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
lean_inc(x_28);
x_29 = lean_apply_1(x_1, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_2);
x_13 = x_24;
x_14 = x_25;
goto block_18;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_apply_8(x_2, x_30, x_19, x_20, x_21, x_22, x_23, x_24, x_25);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_28);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_13 = x_35;
x_14 = x_34;
goto block_18;
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = !lean_is_exclusive(x_32);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_38 = lean_ctor_get(x_32, 0);
lean_dec(x_38);
x_39 = lean_st_ref_take(x_6, x_36);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lake_CacheMap_insertCore(x_4, x_28, x_40);
x_43 = lean_st_ref_set(x_6, x_42, x_41);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
lean_ctor_set(x_43, 0, x_32);
return x_43;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_32);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_48 = lean_ctor_get(x_32, 1);
lean_inc(x_48);
lean_dec(x_32);
x_49 = lean_st_ref_take(x_6, x_36);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lake_CacheMap_insertCore(x_4, x_28, x_50);
x_53 = lean_st_ref_set(x_6, x_52, x_51);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_33);
lean_ctor_set(x_56, 1, x_48);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
return x_57;
}
}
}
else
{
lean_dec(x_32);
lean_dec(x_28);
return x_31;
}
}
}
}
else
{
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_13 = x_24;
x_14 = x_25;
goto block_18;
}
}
}
}
static lean_object* _init_l_Lake_buildArtifactUnlessUpToDate___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_JobM_runFetchM), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_buildArtifactUnlessUpToDate___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_EquipT_lift___boxed), 5, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_buildArtifactUnlessUpToDate___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_buildArtifactUnlessUpToDate___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 3);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
lean_closure_set(x_1, 2, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_buildArtifactUnlessUpToDate___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instMonadWorkspaceJobM___closed__0;
x_2 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__1), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_buildArtifactUnlessUpToDate___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_buildArtifactUnlessUpToDate___closed__4;
x_2 = lean_alloc_closure((void*)(l_Lake_instMonadLiftTOfMonadLift__lake___redArg___lam__0), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_buildArtifactUnlessUpToDate___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_buildArtifactUnlessUpToDate___closed__2;
x_2 = l_Lake_buildArtifactUnlessUpToDate___closed__5;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_buildArtifactUnlessUpToDate___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_buildArtifactUnlessUpToDate___closed__3;
x_2 = l_Lake_buildArtifactUnlessUpToDate___closed__6;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_buildArtifactUnlessUpToDate___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_buildArtifactUnlessUpToDate___closed__2;
x_2 = l_Lake_buildArtifactUnlessUpToDate___closed__7;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_buildArtifactUnlessUpToDate___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_buildArtifactUnlessUpToDate___closed__2;
x_2 = l_Lake_buildArtifactUnlessUpToDate___closed__8;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_buildArtifactUnlessUpToDate___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_buildArtifactUnlessUpToDate___closed__1;
x_2 = l_Lake_buildArtifactUnlessUpToDate___closed__9;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_buildArtifactUnlessUpToDate___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_buildArtifactUnlessUpToDate___closed__0;
x_2 = l_Lake_buildArtifactUnlessUpToDate___closed__10;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_buildArtifactUnlessUpToDate___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instFromJsonFileOutputHash___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_buildArtifactUnlessUpToDate___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("restored artifact from cache to: ", 33, 33);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_25; uint8_t x_26; 
x_25 = l_Lake_instMonadWorkspaceJobM___closed__0;
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_29 = lean_ctor_get(x_25, 1);
x_30 = lean_ctor_get(x_27, 0);
x_31 = lean_ctor_get(x_27, 1);
x_32 = lean_ctor_get(x_27, 4);
lean_dec(x_32);
x_33 = lean_ctor_get(x_27, 3);
lean_dec(x_33);
x_34 = lean_ctor_get(x_27, 2);
lean_dec(x_34);
lean_inc(x_29);
lean_inc(x_31);
x_35 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_35, 0, x_31);
lean_closure_set(x_35, 1, x_29);
lean_inc(x_29);
lean_inc(x_31);
x_36 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_36, 0, x_31);
lean_closure_set(x_36, 1, x_29);
lean_inc(x_35);
lean_inc(x_31);
x_37 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_37, 0, x_31);
lean_closure_set(x_37, 1, x_35);
lean_inc(x_31);
lean_inc(x_30);
x_38 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_38, 0, x_30);
lean_closure_set(x_38, 1, x_31);
lean_closure_set(x_38, 2, x_29);
x_39 = l_Lake_EStateT_instFunctor___redArg(x_30);
x_40 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_40, 0, x_31);
lean_ctor_set(x_27, 4, x_36);
lean_ctor_set(x_27, 3, x_37);
lean_ctor_set(x_27, 2, x_38);
lean_ctor_set(x_27, 1, x_40);
lean_ctor_set(x_27, 0, x_39);
lean_ctor_set(x_25, 1, x_35);
x_41 = l_ReaderT_instMonad___redArg(x_25);
x_42 = l_ReaderT_instMonad___redArg(x_41);
x_43 = l_ReaderT_instMonad___redArg(x_42);
lean_inc(x_43);
x_44 = l_ReaderT_instMonad___redArg(x_43);
x_45 = !lean_is_exclusive(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_46 = lean_ctor_get(x_43, 0);
x_47 = lean_ctor_get(x_43, 1);
lean_dec(x_47);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_48);
x_49 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_49, 0, x_48);
x_50 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_50, 0, x_48);
lean_ctor_set(x_43, 1, x_50);
lean_ctor_set(x_43, 0, x_49);
x_51 = l_Lake_EquipT_instFunctor___redArg(x_43);
x_52 = l_Lake_EquipT_instMonad___redArg(x_44);
x_53 = !lean_is_exclusive(x_11);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_54 = lean_ctor_get(x_11, 0);
x_55 = lean_ctor_get(x_11, 1);
x_56 = l_Lake_buildFileUnlessUpToDate_x27___closed__0;
lean_inc(x_1);
x_57 = lean_string_append(x_1, x_56);
lean_inc(x_57);
x_58 = l_Lake_readTraceFile(x_57, x_54, x_12);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_63 = x_59;
} else {
 lean_dec_ref(x_59);
 x_63 = lean_box(0);
}
lean_inc(x_55);
lean_ctor_set(x_11, 0, x_62);
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_63);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_4);
x_64 = x_6;
x_65 = x_7;
x_66 = x_8;
x_67 = x_9;
x_68 = x_10;
x_69 = x_11;
x_70 = x_60;
goto block_229;
}
else
{
lean_object* x_230; lean_object* x_231; 
x_230 = lean_ctor_get(x_7, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_230, 19);
lean_inc(x_231);
lean_dec(x_230);
if (lean_obj_tag(x_231) == 0)
{
lean_dec(x_63);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_4);
x_64 = x_6;
x_65 = x_7;
x_66 = x_8;
x_67 = x_9;
x_68 = x_10;
x_69 = x_11;
x_70 = x_60;
goto block_229;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint64_t x_318; lean_object* x_319; lean_object* x_320; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
lean_dec(x_231);
x_233 = lean_ctor_get(x_55, 2);
lean_inc(x_233);
x_234 = lean_ctor_get(x_55, 3);
lean_inc(x_234);
x_313 = l_Lake_instMonadWorkspaceJobM;
x_314 = l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___redArg(x_313, x_51);
x_315 = l_Lake_buildArtifactUnlessUpToDate___closed__11;
x_316 = l_Lake_buildArtifactUnlessUpToDate___closed__12;
lean_inc(x_4);
x_317 = l_Lake_instResolveArtifactsFileOutputHashArtifactOfMonadLakeEnvOfMonadLiftTBaseIOOfMonad___redArg(x_4, x_314, x_315, x_52);
x_318 = lean_unbox_uint64(x_233);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_61);
lean_inc(x_6);
x_319 = l_Lake_resolveArtifactsUsing_x3f___at___Lake_buildArtifactUnlessUpToDate_spec__0(x_316, x_317, x_6, x_318, x_61, x_232, x_7, x_8, x_9, x_10, x_11, x_60);
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; 
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; 
x_322 = lean_ctor_get(x_319, 1);
lean_inc(x_322);
lean_dec(x_319);
x_323 = lean_ctor_get(x_320, 1);
lean_inc(x_323);
lean_dec(x_320);
x_324 = l_Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0(x_6, x_1, x_55, x_61, x_234, x_7, x_8, x_9, x_10, x_323, x_322);
lean_dec(x_234);
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
x_327 = lean_unbox(x_326);
lean_dec(x_326);
if (x_327 == 0)
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_328 = lean_ctor_get(x_324, 1);
lean_inc(x_328);
lean_dec(x_324);
x_329 = lean_ctor_get(x_325, 1);
lean_inc(x_329);
lean_dec(x_325);
lean_inc(x_10);
lean_inc(x_1);
x_330 = l_Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_3, x_55, x_57, x_6, x_7, x_8, x_9, x_10, x_329, x_328);
lean_dec(x_57);
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
if (lean_obj_tag(x_331) == 0)
{
lean_object* x_332; lean_object* x_333; 
x_332 = lean_ctor_get(x_330, 1);
lean_inc(x_332);
lean_dec(x_330);
x_333 = lean_ctor_get(x_331, 1);
lean_inc(x_333);
lean_dec(x_331);
x_235 = x_10;
x_236 = x_333;
x_237 = x_332;
goto block_312;
}
else
{
uint8_t x_334; 
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_63);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_1);
x_334 = !lean_is_exclusive(x_330);
if (x_334 == 0)
{
lean_object* x_335; uint8_t x_336; 
x_335 = lean_ctor_get(x_330, 0);
lean_dec(x_335);
x_336 = !lean_is_exclusive(x_331);
if (x_336 == 0)
{
return x_330;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_337 = lean_ctor_get(x_331, 0);
x_338 = lean_ctor_get(x_331, 1);
lean_inc(x_338);
lean_inc(x_337);
lean_dec(x_331);
x_339 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_339, 0, x_337);
lean_ctor_set(x_339, 1, x_338);
lean_ctor_set(x_330, 0, x_339);
return x_330;
}
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_340 = lean_ctor_get(x_330, 1);
lean_inc(x_340);
lean_dec(x_330);
x_341 = lean_ctor_get(x_331, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_331, 1);
lean_inc(x_342);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 x_343 = x_331;
} else {
 lean_dec_ref(x_331);
 x_343 = lean_box(0);
}
if (lean_is_scalar(x_343)) {
 x_344 = lean_alloc_ctor(1, 2, 0);
} else {
 x_344 = x_343;
}
lean_ctor_set(x_344, 0, x_341);
lean_ctor_set(x_344, 1, x_342);
x_345 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_345, 0, x_344);
lean_ctor_set(x_345, 1, x_340);
return x_345;
}
}
}
else
{
lean_object* x_346; lean_object* x_347; 
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_346 = lean_ctor_get(x_324, 1);
lean_inc(x_346);
lean_dec(x_324);
x_347 = lean_ctor_get(x_325, 1);
lean_inc(x_347);
lean_dec(x_325);
x_235 = x_10;
x_236 = x_347;
x_237 = x_346;
goto block_312;
}
}
else
{
lean_object* x_348; uint8_t x_349; 
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_63);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_348 = lean_ctor_get(x_319, 1);
lean_inc(x_348);
lean_dec(x_319);
x_349 = !lean_is_exclusive(x_320);
if (x_349 == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_369; 
x_350 = lean_ctor_get(x_320, 1);
x_351 = lean_ctor_get(x_320, 0);
lean_dec(x_351);
x_352 = lean_ctor_get(x_321, 0);
lean_inc(x_352);
lean_dec(x_321);
x_369 = l_System_FilePath_pathExists(x_1, x_348);
if (x_5 == 0)
{
lean_object* x_370; 
lean_free_object(x_320);
x_370 = lean_ctor_get(x_369, 1);
lean_inc(x_370);
lean_dec(x_369);
x_353 = x_350;
x_354 = x_370;
goto block_368;
}
else
{
lean_object* x_371; uint8_t x_372; 
x_371 = lean_ctor_get(x_369, 0);
lean_inc(x_371);
x_372 = lean_unbox(x_371);
lean_dec(x_371);
if (x_372 == 0)
{
lean_object* x_373; uint8_t x_374; 
x_373 = lean_ctor_get(x_369, 1);
lean_inc(x_373);
lean_dec(x_369);
x_374 = !lean_is_exclusive(x_350);
if (x_374 == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; uint8_t x_382; lean_object* x_383; lean_object* x_384; 
x_375 = lean_ctor_get(x_350, 0);
x_376 = lean_ctor_get(x_352, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_352, 3);
lean_inc(x_377);
x_378 = l_Lake_buildArtifactUnlessUpToDate___closed__13;
x_379 = lean_string_append(x_378, x_1);
x_380 = lean_box(0);
x_381 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_381, 0, x_379);
x_382 = lean_unbox(x_380);
lean_ctor_set_uint8(x_381, sizeof(void*)*1, x_382);
x_383 = lean_array_push(x_375, x_381);
x_384 = l_Lake_copyFile(x_376, x_1, x_373);
lean_dec(x_376);
if (lean_obj_tag(x_384) == 0)
{
lean_object* x_385; uint64_t x_386; lean_object* x_387; 
x_385 = lean_ctor_get(x_384, 1);
lean_inc(x_385);
lean_dec(x_384);
x_386 = lean_unbox_uint64(x_377);
lean_dec(x_377);
lean_inc(x_1);
x_387 = l_Lake_writeFileHash(x_1, x_386, x_385);
if (lean_obj_tag(x_387) == 0)
{
lean_object* x_388; 
lean_free_object(x_320);
x_388 = lean_ctor_get(x_387, 1);
lean_inc(x_388);
lean_dec(x_387);
lean_ctor_set(x_350, 0, x_383);
x_353 = x_350;
x_354 = x_388;
goto block_368;
}
else
{
uint8_t x_389; 
lean_dec(x_352);
lean_dec(x_61);
lean_dec(x_1);
x_389 = !lean_is_exclusive(x_387);
if (x_389 == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; uint8_t x_394; lean_object* x_395; lean_object* x_396; 
x_390 = lean_ctor_get(x_387, 0);
x_391 = lean_io_error_to_string(x_390);
x_392 = lean_box(3);
x_393 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_393, 0, x_391);
x_394 = lean_unbox(x_392);
lean_ctor_set_uint8(x_393, sizeof(void*)*1, x_394);
x_395 = lean_array_get_size(x_383);
x_396 = lean_array_push(x_383, x_393);
lean_ctor_set(x_350, 0, x_396);
lean_ctor_set_tag(x_320, 1);
lean_ctor_set(x_320, 0, x_395);
lean_ctor_set_tag(x_387, 0);
lean_ctor_set(x_387, 0, x_320);
return x_387;
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_397 = lean_ctor_get(x_387, 0);
x_398 = lean_ctor_get(x_387, 1);
lean_inc(x_398);
lean_inc(x_397);
lean_dec(x_387);
x_399 = lean_io_error_to_string(x_397);
x_400 = lean_box(3);
x_401 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_401, 0, x_399);
x_402 = lean_unbox(x_400);
lean_ctor_set_uint8(x_401, sizeof(void*)*1, x_402);
x_403 = lean_array_get_size(x_383);
x_404 = lean_array_push(x_383, x_401);
lean_ctor_set(x_350, 0, x_404);
lean_ctor_set_tag(x_320, 1);
lean_ctor_set(x_320, 0, x_403);
x_405 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_405, 0, x_320);
lean_ctor_set(x_405, 1, x_398);
return x_405;
}
}
}
else
{
uint8_t x_406; 
lean_dec(x_377);
lean_dec(x_352);
lean_dec(x_61);
lean_dec(x_1);
x_406 = !lean_is_exclusive(x_384);
if (x_406 == 0)
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; uint8_t x_411; lean_object* x_412; lean_object* x_413; 
x_407 = lean_ctor_get(x_384, 0);
x_408 = lean_io_error_to_string(x_407);
x_409 = lean_box(3);
x_410 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_410, 0, x_408);
x_411 = lean_unbox(x_409);
lean_ctor_set_uint8(x_410, sizeof(void*)*1, x_411);
x_412 = lean_array_get_size(x_383);
x_413 = lean_array_push(x_383, x_410);
lean_ctor_set(x_350, 0, x_413);
lean_ctor_set_tag(x_320, 1);
lean_ctor_set(x_320, 0, x_412);
lean_ctor_set_tag(x_384, 0);
lean_ctor_set(x_384, 0, x_320);
return x_384;
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; uint8_t x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_414 = lean_ctor_get(x_384, 0);
x_415 = lean_ctor_get(x_384, 1);
lean_inc(x_415);
lean_inc(x_414);
lean_dec(x_384);
x_416 = lean_io_error_to_string(x_414);
x_417 = lean_box(3);
x_418 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_418, 0, x_416);
x_419 = lean_unbox(x_417);
lean_ctor_set_uint8(x_418, sizeof(void*)*1, x_419);
x_420 = lean_array_get_size(x_383);
x_421 = lean_array_push(x_383, x_418);
lean_ctor_set(x_350, 0, x_421);
lean_ctor_set_tag(x_320, 1);
lean_ctor_set(x_320, 0, x_420);
x_422 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_422, 0, x_320);
lean_ctor_set(x_422, 1, x_415);
return x_422;
}
}
}
else
{
lean_object* x_423; uint8_t x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; uint8_t x_432; lean_object* x_433; lean_object* x_434; 
x_423 = lean_ctor_get(x_350, 0);
x_424 = lean_ctor_get_uint8(x_350, sizeof(void*)*2);
x_425 = lean_ctor_get(x_350, 1);
lean_inc(x_425);
lean_inc(x_423);
lean_dec(x_350);
x_426 = lean_ctor_get(x_352, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_352, 3);
lean_inc(x_427);
x_428 = l_Lake_buildArtifactUnlessUpToDate___closed__13;
x_429 = lean_string_append(x_428, x_1);
x_430 = lean_box(0);
x_431 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_431, 0, x_429);
x_432 = lean_unbox(x_430);
lean_ctor_set_uint8(x_431, sizeof(void*)*1, x_432);
x_433 = lean_array_push(x_423, x_431);
x_434 = l_Lake_copyFile(x_426, x_1, x_373);
lean_dec(x_426);
if (lean_obj_tag(x_434) == 0)
{
lean_object* x_435; uint64_t x_436; lean_object* x_437; 
x_435 = lean_ctor_get(x_434, 1);
lean_inc(x_435);
lean_dec(x_434);
x_436 = lean_unbox_uint64(x_427);
lean_dec(x_427);
lean_inc(x_1);
x_437 = l_Lake_writeFileHash(x_1, x_436, x_435);
if (lean_obj_tag(x_437) == 0)
{
lean_object* x_438; lean_object* x_439; 
lean_free_object(x_320);
x_438 = lean_ctor_get(x_437, 1);
lean_inc(x_438);
lean_dec(x_437);
x_439 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_439, 0, x_433);
lean_ctor_set(x_439, 1, x_425);
lean_ctor_set_uint8(x_439, sizeof(void*)*2, x_424);
x_353 = x_439;
x_354 = x_438;
goto block_368;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; uint8_t x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
lean_dec(x_352);
lean_dec(x_61);
lean_dec(x_1);
x_440 = lean_ctor_get(x_437, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_437, 1);
lean_inc(x_441);
if (lean_is_exclusive(x_437)) {
 lean_ctor_release(x_437, 0);
 lean_ctor_release(x_437, 1);
 x_442 = x_437;
} else {
 lean_dec_ref(x_437);
 x_442 = lean_box(0);
}
x_443 = lean_io_error_to_string(x_440);
x_444 = lean_box(3);
x_445 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_445, 0, x_443);
x_446 = lean_unbox(x_444);
lean_ctor_set_uint8(x_445, sizeof(void*)*1, x_446);
x_447 = lean_array_get_size(x_433);
x_448 = lean_array_push(x_433, x_445);
x_449 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_449, 0, x_448);
lean_ctor_set(x_449, 1, x_425);
lean_ctor_set_uint8(x_449, sizeof(void*)*2, x_424);
lean_ctor_set_tag(x_320, 1);
lean_ctor_set(x_320, 1, x_449);
lean_ctor_set(x_320, 0, x_447);
if (lean_is_scalar(x_442)) {
 x_450 = lean_alloc_ctor(0, 2, 0);
} else {
 x_450 = x_442;
 lean_ctor_set_tag(x_450, 0);
}
lean_ctor_set(x_450, 0, x_320);
lean_ctor_set(x_450, 1, x_441);
return x_450;
}
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; uint8_t x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; 
lean_dec(x_427);
lean_dec(x_352);
lean_dec(x_61);
lean_dec(x_1);
x_451 = lean_ctor_get(x_434, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_434, 1);
lean_inc(x_452);
if (lean_is_exclusive(x_434)) {
 lean_ctor_release(x_434, 0);
 lean_ctor_release(x_434, 1);
 x_453 = x_434;
} else {
 lean_dec_ref(x_434);
 x_453 = lean_box(0);
}
x_454 = lean_io_error_to_string(x_451);
x_455 = lean_box(3);
x_456 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_456, 0, x_454);
x_457 = lean_unbox(x_455);
lean_ctor_set_uint8(x_456, sizeof(void*)*1, x_457);
x_458 = lean_array_get_size(x_433);
x_459 = lean_array_push(x_433, x_456);
x_460 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_460, 0, x_459);
lean_ctor_set(x_460, 1, x_425);
lean_ctor_set_uint8(x_460, sizeof(void*)*2, x_424);
lean_ctor_set_tag(x_320, 1);
lean_ctor_set(x_320, 1, x_460);
lean_ctor_set(x_320, 0, x_458);
if (lean_is_scalar(x_453)) {
 x_461 = lean_alloc_ctor(0, 2, 0);
} else {
 x_461 = x_453;
 lean_ctor_set_tag(x_461, 0);
}
lean_ctor_set(x_461, 0, x_320);
lean_ctor_set(x_461, 1, x_452);
return x_461;
}
}
}
else
{
lean_object* x_462; 
lean_free_object(x_320);
x_462 = lean_ctor_get(x_369, 1);
lean_inc(x_462);
lean_dec(x_369);
x_353 = x_350;
x_354 = x_462;
goto block_368;
}
}
block_368:
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; 
x_355 = l_Lake_SavedTrace_replayIfExists___redArg(x_61, x_353, x_354);
lean_dec(x_61);
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_356, 1);
lean_inc(x_357);
lean_dec(x_356);
x_358 = lean_ctor_get(x_355, 1);
lean_inc(x_358);
lean_dec(x_355);
x_359 = !lean_is_exclusive(x_357);
if (x_359 == 0)
{
lean_object* x_360; lean_object* x_361; 
x_360 = lean_ctor_get(x_357, 1);
lean_dec(x_360);
lean_inc(x_352);
x_361 = l_Lake_Artifact_trace(x_352);
lean_ctor_set(x_357, 1, x_361);
if (x_5 == 0)
{
lean_object* x_362; 
lean_dec(x_1);
x_362 = lean_ctor_get(x_352, 0);
lean_inc(x_362);
lean_dec(x_352);
x_13 = x_358;
x_14 = x_357;
x_15 = x_362;
goto block_18;
}
else
{
lean_dec(x_352);
x_13 = x_358;
x_14 = x_357;
x_15 = x_1;
goto block_18;
}
}
else
{
lean_object* x_363; uint8_t x_364; lean_object* x_365; lean_object* x_366; 
x_363 = lean_ctor_get(x_357, 0);
x_364 = lean_ctor_get_uint8(x_357, sizeof(void*)*2);
lean_inc(x_363);
lean_dec(x_357);
lean_inc(x_352);
x_365 = l_Lake_Artifact_trace(x_352);
x_366 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_366, 0, x_363);
lean_ctor_set(x_366, 1, x_365);
lean_ctor_set_uint8(x_366, sizeof(void*)*2, x_364);
if (x_5 == 0)
{
lean_object* x_367; 
lean_dec(x_1);
x_367 = lean_ctor_get(x_352, 0);
lean_inc(x_367);
lean_dec(x_352);
x_13 = x_358;
x_14 = x_366;
x_15 = x_367;
goto block_18;
}
else
{
lean_dec(x_352);
x_13 = x_358;
x_14 = x_366;
x_15 = x_1;
goto block_18;
}
}
}
}
else
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_478; 
x_463 = lean_ctor_get(x_320, 1);
lean_inc(x_463);
lean_dec(x_320);
x_464 = lean_ctor_get(x_321, 0);
lean_inc(x_464);
lean_dec(x_321);
x_478 = l_System_FilePath_pathExists(x_1, x_348);
if (x_5 == 0)
{
lean_object* x_479; 
x_479 = lean_ctor_get(x_478, 1);
lean_inc(x_479);
lean_dec(x_478);
x_465 = x_463;
x_466 = x_479;
goto block_477;
}
else
{
lean_object* x_480; uint8_t x_481; 
x_480 = lean_ctor_get(x_478, 0);
lean_inc(x_480);
x_481 = lean_unbox(x_480);
lean_dec(x_480);
if (x_481 == 0)
{
lean_object* x_482; lean_object* x_483; uint8_t x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; uint8_t x_493; lean_object* x_494; lean_object* x_495; 
x_482 = lean_ctor_get(x_478, 1);
lean_inc(x_482);
lean_dec(x_478);
x_483 = lean_ctor_get(x_463, 0);
lean_inc(x_483);
x_484 = lean_ctor_get_uint8(x_463, sizeof(void*)*2);
x_485 = lean_ctor_get(x_463, 1);
lean_inc(x_485);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 x_486 = x_463;
} else {
 lean_dec_ref(x_463);
 x_486 = lean_box(0);
}
x_487 = lean_ctor_get(x_464, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_464, 3);
lean_inc(x_488);
x_489 = l_Lake_buildArtifactUnlessUpToDate___closed__13;
x_490 = lean_string_append(x_489, x_1);
x_491 = lean_box(0);
x_492 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_492, 0, x_490);
x_493 = lean_unbox(x_491);
lean_ctor_set_uint8(x_492, sizeof(void*)*1, x_493);
x_494 = lean_array_push(x_483, x_492);
x_495 = l_Lake_copyFile(x_487, x_1, x_482);
lean_dec(x_487);
if (lean_obj_tag(x_495) == 0)
{
lean_object* x_496; uint64_t x_497; lean_object* x_498; 
x_496 = lean_ctor_get(x_495, 1);
lean_inc(x_496);
lean_dec(x_495);
x_497 = lean_unbox_uint64(x_488);
lean_dec(x_488);
lean_inc(x_1);
x_498 = l_Lake_writeFileHash(x_1, x_497, x_496);
if (lean_obj_tag(x_498) == 0)
{
lean_object* x_499; lean_object* x_500; 
x_499 = lean_ctor_get(x_498, 1);
lean_inc(x_499);
lean_dec(x_498);
if (lean_is_scalar(x_486)) {
 x_500 = lean_alloc_ctor(0, 2, 1);
} else {
 x_500 = x_486;
}
lean_ctor_set(x_500, 0, x_494);
lean_ctor_set(x_500, 1, x_485);
lean_ctor_set_uint8(x_500, sizeof(void*)*2, x_484);
x_465 = x_500;
x_466 = x_499;
goto block_477;
}
else
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; uint8_t x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
lean_dec(x_464);
lean_dec(x_61);
lean_dec(x_1);
x_501 = lean_ctor_get(x_498, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_498, 1);
lean_inc(x_502);
if (lean_is_exclusive(x_498)) {
 lean_ctor_release(x_498, 0);
 lean_ctor_release(x_498, 1);
 x_503 = x_498;
} else {
 lean_dec_ref(x_498);
 x_503 = lean_box(0);
}
x_504 = lean_io_error_to_string(x_501);
x_505 = lean_box(3);
x_506 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_506, 0, x_504);
x_507 = lean_unbox(x_505);
lean_ctor_set_uint8(x_506, sizeof(void*)*1, x_507);
x_508 = lean_array_get_size(x_494);
x_509 = lean_array_push(x_494, x_506);
if (lean_is_scalar(x_486)) {
 x_510 = lean_alloc_ctor(0, 2, 1);
} else {
 x_510 = x_486;
}
lean_ctor_set(x_510, 0, x_509);
lean_ctor_set(x_510, 1, x_485);
lean_ctor_set_uint8(x_510, sizeof(void*)*2, x_484);
x_511 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_511, 0, x_508);
lean_ctor_set(x_511, 1, x_510);
if (lean_is_scalar(x_503)) {
 x_512 = lean_alloc_ctor(0, 2, 0);
} else {
 x_512 = x_503;
 lean_ctor_set_tag(x_512, 0);
}
lean_ctor_set(x_512, 0, x_511);
lean_ctor_set(x_512, 1, x_502);
return x_512;
}
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; uint8_t x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; 
lean_dec(x_488);
lean_dec(x_464);
lean_dec(x_61);
lean_dec(x_1);
x_513 = lean_ctor_get(x_495, 0);
lean_inc(x_513);
x_514 = lean_ctor_get(x_495, 1);
lean_inc(x_514);
if (lean_is_exclusive(x_495)) {
 lean_ctor_release(x_495, 0);
 lean_ctor_release(x_495, 1);
 x_515 = x_495;
} else {
 lean_dec_ref(x_495);
 x_515 = lean_box(0);
}
x_516 = lean_io_error_to_string(x_513);
x_517 = lean_box(3);
x_518 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_518, 0, x_516);
x_519 = lean_unbox(x_517);
lean_ctor_set_uint8(x_518, sizeof(void*)*1, x_519);
x_520 = lean_array_get_size(x_494);
x_521 = lean_array_push(x_494, x_518);
if (lean_is_scalar(x_486)) {
 x_522 = lean_alloc_ctor(0, 2, 1);
} else {
 x_522 = x_486;
}
lean_ctor_set(x_522, 0, x_521);
lean_ctor_set(x_522, 1, x_485);
lean_ctor_set_uint8(x_522, sizeof(void*)*2, x_484);
x_523 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_523, 0, x_520);
lean_ctor_set(x_523, 1, x_522);
if (lean_is_scalar(x_515)) {
 x_524 = lean_alloc_ctor(0, 2, 0);
} else {
 x_524 = x_515;
 lean_ctor_set_tag(x_524, 0);
}
lean_ctor_set(x_524, 0, x_523);
lean_ctor_set(x_524, 1, x_514);
return x_524;
}
}
else
{
lean_object* x_525; 
x_525 = lean_ctor_get(x_478, 1);
lean_inc(x_525);
lean_dec(x_478);
x_465 = x_463;
x_466 = x_525;
goto block_477;
}
}
block_477:
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; uint8_t x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_467 = l_Lake_SavedTrace_replayIfExists___redArg(x_61, x_465, x_466);
lean_dec(x_61);
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_468, 1);
lean_inc(x_469);
lean_dec(x_468);
x_470 = lean_ctor_get(x_467, 1);
lean_inc(x_470);
lean_dec(x_467);
x_471 = lean_ctor_get(x_469, 0);
lean_inc(x_471);
x_472 = lean_ctor_get_uint8(x_469, sizeof(void*)*2);
if (lean_is_exclusive(x_469)) {
 lean_ctor_release(x_469, 0);
 lean_ctor_release(x_469, 1);
 x_473 = x_469;
} else {
 lean_dec_ref(x_469);
 x_473 = lean_box(0);
}
lean_inc(x_464);
x_474 = l_Lake_Artifact_trace(x_464);
if (lean_is_scalar(x_473)) {
 x_475 = lean_alloc_ctor(0, 2, 1);
} else {
 x_475 = x_473;
}
lean_ctor_set(x_475, 0, x_471);
lean_ctor_set(x_475, 1, x_474);
lean_ctor_set_uint8(x_475, sizeof(void*)*2, x_472);
if (x_5 == 0)
{
lean_object* x_476; 
lean_dec(x_1);
x_476 = lean_ctor_get(x_464, 0);
lean_inc(x_476);
lean_dec(x_464);
x_13 = x_470;
x_14 = x_475;
x_15 = x_476;
goto block_18;
}
else
{
lean_dec(x_464);
x_13 = x_470;
x_14 = x_475;
x_15 = x_1;
goto block_18;
}
}
}
}
}
else
{
uint8_t x_526; 
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_63);
lean_dec(x_61);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_526 = !lean_is_exclusive(x_319);
if (x_526 == 0)
{
lean_object* x_527; uint8_t x_528; 
x_527 = lean_ctor_get(x_319, 0);
lean_dec(x_527);
x_528 = !lean_is_exclusive(x_320);
if (x_528 == 0)
{
return x_319;
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_529 = lean_ctor_get(x_320, 0);
x_530 = lean_ctor_get(x_320, 1);
lean_inc(x_530);
lean_inc(x_529);
lean_dec(x_320);
x_531 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_531, 0, x_529);
lean_ctor_set(x_531, 1, x_530);
lean_ctor_set(x_319, 0, x_531);
return x_319;
}
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; 
x_532 = lean_ctor_get(x_319, 1);
lean_inc(x_532);
lean_dec(x_319);
x_533 = lean_ctor_get(x_320, 0);
lean_inc(x_533);
x_534 = lean_ctor_get(x_320, 1);
lean_inc(x_534);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 lean_ctor_release(x_320, 1);
 x_535 = x_320;
} else {
 lean_dec_ref(x_320);
 x_535 = lean_box(0);
}
if (lean_is_scalar(x_535)) {
 x_536 = lean_alloc_ctor(1, 2, 0);
} else {
 x_536 = x_535;
}
lean_ctor_set(x_536, 0, x_533);
lean_ctor_set(x_536, 1, x_534);
x_537 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_537, 0, x_536);
lean_ctor_set(x_537, 1, x_532);
return x_537;
}
}
block_312:
{
lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_238 = lean_ctor_get(x_235, 1);
lean_inc(x_238);
lean_dec(x_235);
x_239 = lean_ctor_get(x_238, 1);
lean_inc(x_239);
lean_dec(x_238);
x_240 = !lean_is_exclusive(x_236);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_241 = lean_ctor_get(x_236, 0);
x_242 = lean_ctor_get(x_236, 1);
x_243 = lean_ctor_get(x_239, 6);
lean_inc(x_243);
lean_dec(x_239);
lean_inc(x_1);
x_244 = l_Lake_Cache_saveArtifact(x_243, x_1, x_4, x_3, x_237);
lean_dec(x_4);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint64_t x_252; lean_object* x_253; lean_object* x_254; uint64_t x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_242);
lean_dec(x_63);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = lean_st_ref_take(x_232, x_246);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
x_250 = lean_ctor_get(x_245, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_245, 3);
lean_inc(x_251);
x_252 = lean_unbox_uint64(x_251);
lean_dec(x_251);
x_253 = lean_uint64_to_nat(x_252);
x_254 = l_Lean_bignumToJson(x_253);
x_255 = lean_unbox_uint64(x_233);
lean_dec(x_233);
x_256 = l_Lake_CacheMap_insertCore(x_255, x_254, x_248);
x_257 = lean_st_ref_set(x_232, x_256, x_249);
lean_dec(x_232);
x_258 = lean_ctor_get(x_257, 1);
lean_inc(x_258);
lean_dec(x_257);
x_259 = l_Lake_Artifact_trace(x_245);
lean_ctor_set(x_236, 1, x_259);
if (x_5 == 0)
{
lean_dec(x_1);
x_19 = x_258;
x_20 = x_236;
x_21 = x_250;
goto block_24;
}
else
{
lean_dec(x_250);
x_19 = x_258;
x_20 = x_236;
x_21 = x_1;
goto block_24;
}
}
else
{
uint8_t x_260; 
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_1);
x_260 = !lean_is_exclusive(x_244);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_261 = lean_ctor_get(x_244, 0);
x_262 = lean_io_error_to_string(x_261);
x_263 = lean_box(3);
x_264 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_264, 0, x_262);
x_265 = lean_unbox(x_263);
lean_ctor_set_uint8(x_264, sizeof(void*)*1, x_265);
x_266 = lean_array_get_size(x_241);
x_267 = lean_array_push(x_241, x_264);
lean_ctor_set(x_236, 0, x_267);
if (lean_is_scalar(x_63)) {
 x_268 = lean_alloc_ctor(1, 2, 0);
} else {
 x_268 = x_63;
 lean_ctor_set_tag(x_268, 1);
}
lean_ctor_set(x_268, 0, x_266);
lean_ctor_set(x_268, 1, x_236);
lean_ctor_set_tag(x_244, 0);
lean_ctor_set(x_244, 0, x_268);
return x_244;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_269 = lean_ctor_get(x_244, 0);
x_270 = lean_ctor_get(x_244, 1);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_244);
x_271 = lean_io_error_to_string(x_269);
x_272 = lean_box(3);
x_273 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_273, 0, x_271);
x_274 = lean_unbox(x_272);
lean_ctor_set_uint8(x_273, sizeof(void*)*1, x_274);
x_275 = lean_array_get_size(x_241);
x_276 = lean_array_push(x_241, x_273);
lean_ctor_set(x_236, 0, x_276);
if (lean_is_scalar(x_63)) {
 x_277 = lean_alloc_ctor(1, 2, 0);
} else {
 x_277 = x_63;
 lean_ctor_set_tag(x_277, 1);
}
lean_ctor_set(x_277, 0, x_275);
lean_ctor_set(x_277, 1, x_236);
x_278 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_270);
return x_278;
}
}
}
else
{
lean_object* x_279; uint8_t x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_279 = lean_ctor_get(x_236, 0);
x_280 = lean_ctor_get_uint8(x_236, sizeof(void*)*2);
x_281 = lean_ctor_get(x_236, 1);
lean_inc(x_281);
lean_inc(x_279);
lean_dec(x_236);
x_282 = lean_ctor_get(x_239, 6);
lean_inc(x_282);
lean_dec(x_239);
lean_inc(x_1);
x_283 = l_Lake_Cache_saveArtifact(x_282, x_1, x_4, x_3, x_237);
lean_dec(x_4);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint64_t x_291; lean_object* x_292; lean_object* x_293; uint64_t x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_281);
lean_dec(x_63);
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
lean_dec(x_283);
x_286 = lean_st_ref_take(x_232, x_285);
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
x_289 = lean_ctor_get(x_284, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_284, 3);
lean_inc(x_290);
x_291 = lean_unbox_uint64(x_290);
lean_dec(x_290);
x_292 = lean_uint64_to_nat(x_291);
x_293 = l_Lean_bignumToJson(x_292);
x_294 = lean_unbox_uint64(x_233);
lean_dec(x_233);
x_295 = l_Lake_CacheMap_insertCore(x_294, x_293, x_287);
x_296 = lean_st_ref_set(x_232, x_295, x_288);
lean_dec(x_232);
x_297 = lean_ctor_get(x_296, 1);
lean_inc(x_297);
lean_dec(x_296);
x_298 = l_Lake_Artifact_trace(x_284);
x_299 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_299, 0, x_279);
lean_ctor_set(x_299, 1, x_298);
lean_ctor_set_uint8(x_299, sizeof(void*)*2, x_280);
if (x_5 == 0)
{
lean_dec(x_1);
x_19 = x_297;
x_20 = x_299;
x_21 = x_289;
goto block_24;
}
else
{
lean_dec(x_289);
x_19 = x_297;
x_20 = x_299;
x_21 = x_1;
goto block_24;
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_1);
x_300 = lean_ctor_get(x_283, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_283, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_302 = x_283;
} else {
 lean_dec_ref(x_283);
 x_302 = lean_box(0);
}
x_303 = lean_io_error_to_string(x_300);
x_304 = lean_box(3);
x_305 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_305, 0, x_303);
x_306 = lean_unbox(x_304);
lean_ctor_set_uint8(x_305, sizeof(void*)*1, x_306);
x_307 = lean_array_get_size(x_279);
x_308 = lean_array_push(x_279, x_305);
x_309 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_281);
lean_ctor_set_uint8(x_309, sizeof(void*)*2, x_280);
if (lean_is_scalar(x_63)) {
 x_310 = lean_alloc_ctor(1, 2, 0);
} else {
 x_310 = x_63;
 lean_ctor_set_tag(x_310, 1);
}
lean_ctor_set(x_310, 0, x_307);
lean_ctor_set(x_310, 1, x_309);
if (lean_is_scalar(x_302)) {
 x_311 = lean_alloc_ctor(0, 2, 0);
} else {
 x_311 = x_302;
 lean_ctor_set_tag(x_311, 0);
}
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_301);
return x_311;
}
}
}
}
}
block_229:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = lean_ctor_get(x_55, 3);
lean_inc(x_71);
x_72 = l_Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0(x_64, x_1, x_55, x_61, x_71, x_65, x_66, x_67, x_68, x_69, x_70);
lean_dec(x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
lean_dec(x_72);
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
lean_dec(x_73);
lean_inc(x_1);
x_78 = l_Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_3, x_55, x_57, x_64, x_65, x_66, x_67, x_68, x_77, x_76);
lean_dec(x_57);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_82 = !lean_is_exclusive(x_79);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = lean_ctor_get(x_79, 0);
x_84 = lean_ctor_get(x_79, 1);
lean_dec(x_84);
x_85 = !lean_is_exclusive(x_80);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; uint64_t x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_80, 0);
x_87 = lean_ctor_get(x_80, 1);
x_88 = lean_unbox_uint64(x_83);
lean_inc(x_1);
x_89 = l_Lake_writeFileHash(x_1, x_88, x_81);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; uint64_t x_91; lean_object* x_92; uint8_t x_93; 
lean_dec(x_87);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_91 = lean_unbox_uint64(x_83);
lean_dec(x_83);
lean_inc(x_1);
x_92 = l_Lake_computeArtifactTrace(x_1, x_1, x_91, x_90);
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_92, 0);
lean_ctor_set(x_80, 1, x_94);
lean_ctor_set(x_79, 0, x_1);
lean_ctor_set(x_92, 0, x_79);
return x_92;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_92, 0);
x_96 = lean_ctor_get(x_92, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_92);
lean_ctor_set(x_80, 1, x_95);
lean_ctor_set(x_79, 0, x_1);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_79);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
else
{
uint8_t x_98; 
lean_dec(x_83);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_89);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; 
x_99 = lean_ctor_get(x_89, 0);
x_100 = lean_io_error_to_string(x_99);
x_101 = lean_box(3);
x_102 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_102, 0, x_100);
x_103 = lean_unbox(x_101);
lean_ctor_set_uint8(x_102, sizeof(void*)*1, x_103);
x_104 = lean_array_get_size(x_86);
x_105 = lean_array_push(x_86, x_102);
lean_ctor_set(x_80, 0, x_105);
lean_ctor_set_tag(x_79, 1);
lean_ctor_set(x_79, 0, x_104);
lean_ctor_set_tag(x_89, 0);
lean_ctor_set(x_89, 0, x_79);
return x_89;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_106 = lean_ctor_get(x_89, 0);
x_107 = lean_ctor_get(x_89, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_89);
x_108 = lean_io_error_to_string(x_106);
x_109 = lean_box(3);
x_110 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_110, 0, x_108);
x_111 = lean_unbox(x_109);
lean_ctor_set_uint8(x_110, sizeof(void*)*1, x_111);
x_112 = lean_array_get_size(x_86);
x_113 = lean_array_push(x_86, x_110);
lean_ctor_set(x_80, 0, x_113);
lean_ctor_set_tag(x_79, 1);
lean_ctor_set(x_79, 0, x_112);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_79);
lean_ctor_set(x_114, 1, x_107);
return x_114;
}
}
}
else
{
lean_object* x_115; uint8_t x_116; lean_object* x_117; uint64_t x_118; lean_object* x_119; 
x_115 = lean_ctor_get(x_80, 0);
x_116 = lean_ctor_get_uint8(x_80, sizeof(void*)*2);
x_117 = lean_ctor_get(x_80, 1);
lean_inc(x_117);
lean_inc(x_115);
lean_dec(x_80);
x_118 = lean_unbox_uint64(x_83);
lean_inc(x_1);
x_119 = l_Lake_writeFileHash(x_1, x_118, x_81);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; uint64_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_117);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_121 = lean_unbox_uint64(x_83);
lean_dec(x_83);
lean_inc(x_1);
x_122 = l_Lake_computeArtifactTrace(x_1, x_1, x_121, x_120);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_125 = x_122;
} else {
 lean_dec_ref(x_122);
 x_125 = lean_box(0);
}
x_126 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_126, 0, x_115);
lean_ctor_set(x_126, 1, x_123);
lean_ctor_set_uint8(x_126, sizeof(void*)*2, x_116);
lean_ctor_set(x_79, 1, x_126);
lean_ctor_set(x_79, 0, x_1);
if (lean_is_scalar(x_125)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_125;
}
lean_ctor_set(x_127, 0, x_79);
lean_ctor_set(x_127, 1, x_124);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_83);
lean_dec(x_1);
x_128 = lean_ctor_get(x_119, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_119, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_130 = x_119;
} else {
 lean_dec_ref(x_119);
 x_130 = lean_box(0);
}
x_131 = lean_io_error_to_string(x_128);
x_132 = lean_box(3);
x_133 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_133, 0, x_131);
x_134 = lean_unbox(x_132);
lean_ctor_set_uint8(x_133, sizeof(void*)*1, x_134);
x_135 = lean_array_get_size(x_115);
x_136 = lean_array_push(x_115, x_133);
x_137 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_117);
lean_ctor_set_uint8(x_137, sizeof(void*)*2, x_116);
lean_ctor_set_tag(x_79, 1);
lean_ctor_set(x_79, 1, x_137);
lean_ctor_set(x_79, 0, x_135);
if (lean_is_scalar(x_130)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_130;
 lean_ctor_set_tag(x_138, 0);
}
lean_ctor_set(x_138, 0, x_79);
lean_ctor_set(x_138, 1, x_129);
return x_138;
}
}
}
else
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; uint64_t x_144; lean_object* x_145; 
x_139 = lean_ctor_get(x_79, 0);
lean_inc(x_139);
lean_dec(x_79);
x_140 = lean_ctor_get(x_80, 0);
lean_inc(x_140);
x_141 = lean_ctor_get_uint8(x_80, sizeof(void*)*2);
x_142 = lean_ctor_get(x_80, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_143 = x_80;
} else {
 lean_dec_ref(x_80);
 x_143 = lean_box(0);
}
x_144 = lean_unbox_uint64(x_139);
lean_inc(x_1);
x_145 = l_Lake_writeFileHash(x_1, x_144, x_81);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; uint64_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_142);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_dec(x_145);
x_147 = lean_unbox_uint64(x_139);
lean_dec(x_139);
lean_inc(x_1);
x_148 = l_Lake_computeArtifactTrace(x_1, x_1, x_147, x_146);
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
if (lean_is_scalar(x_143)) {
 x_152 = lean_alloc_ctor(0, 2, 1);
} else {
 x_152 = x_143;
}
lean_ctor_set(x_152, 0, x_140);
lean_ctor_set(x_152, 1, x_149);
lean_ctor_set_uint8(x_152, sizeof(void*)*2, x_141);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_1);
lean_ctor_set(x_153, 1, x_152);
if (lean_is_scalar(x_151)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_151;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_150);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_139);
lean_dec(x_1);
x_155 = lean_ctor_get(x_145, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_145, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_157 = x_145;
} else {
 lean_dec_ref(x_145);
 x_157 = lean_box(0);
}
x_158 = lean_io_error_to_string(x_155);
x_159 = lean_box(3);
x_160 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_160, 0, x_158);
x_161 = lean_unbox(x_159);
lean_ctor_set_uint8(x_160, sizeof(void*)*1, x_161);
x_162 = lean_array_get_size(x_140);
x_163 = lean_array_push(x_140, x_160);
if (lean_is_scalar(x_143)) {
 x_164 = lean_alloc_ctor(0, 2, 1);
} else {
 x_164 = x_143;
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_142);
lean_ctor_set_uint8(x_164, sizeof(void*)*2, x_141);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_164);
if (lean_is_scalar(x_157)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_157;
 lean_ctor_set_tag(x_166, 0);
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_156);
return x_166;
}
}
}
else
{
uint8_t x_167; 
lean_dec(x_1);
x_167 = !lean_is_exclusive(x_78);
if (x_167 == 0)
{
lean_object* x_168; uint8_t x_169; 
x_168 = lean_ctor_get(x_78, 0);
lean_dec(x_168);
x_169 = !lean_is_exclusive(x_79);
if (x_169 == 0)
{
return x_78;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_79, 0);
x_171 = lean_ctor_get(x_79, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_79);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
lean_ctor_set(x_78, 0, x_172);
return x_78;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_173 = lean_ctor_get(x_78, 1);
lean_inc(x_173);
lean_dec(x_78);
x_174 = lean_ctor_get(x_79, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_79, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_176 = x_79;
} else {
 lean_dec_ref(x_79);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_173);
return x_178;
}
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_2);
x_179 = lean_ctor_get(x_72, 1);
lean_inc(x_179);
lean_dec(x_72);
x_180 = lean_ctor_get(x_73, 1);
lean_inc(x_180);
lean_dec(x_73);
lean_inc(x_1);
x_181 = l_Lake_fetchFileHash___redArg(x_1, x_3, x_68, x_180, x_179);
lean_dec(x_68);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; uint8_t x_184; 
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = !lean_is_exclusive(x_182);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; uint64_t x_187; lean_object* x_188; uint8_t x_189; 
x_185 = lean_ctor_get(x_182, 0);
x_186 = lean_ctor_get(x_182, 1);
x_187 = lean_unbox_uint64(x_185);
lean_dec(x_185);
lean_inc(x_1);
x_188 = l_Lake_computeArtifactTrace(x_1, x_1, x_187, x_183);
x_189 = !lean_is_exclusive(x_188);
if (x_189 == 0)
{
uint8_t x_190; 
x_190 = !lean_is_exclusive(x_186);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_188, 0);
x_192 = lean_ctor_get(x_186, 1);
lean_dec(x_192);
lean_ctor_set(x_186, 1, x_191);
lean_ctor_set(x_182, 0, x_1);
lean_ctor_set(x_188, 0, x_182);
return x_188;
}
else
{
lean_object* x_193; lean_object* x_194; uint8_t x_195; lean_object* x_196; 
x_193 = lean_ctor_get(x_188, 0);
x_194 = lean_ctor_get(x_186, 0);
x_195 = lean_ctor_get_uint8(x_186, sizeof(void*)*2);
lean_inc(x_194);
lean_dec(x_186);
x_196 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_193);
lean_ctor_set_uint8(x_196, sizeof(void*)*2, x_195);
lean_ctor_set(x_182, 1, x_196);
lean_ctor_set(x_182, 0, x_1);
lean_ctor_set(x_188, 0, x_182);
return x_188;
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_197 = lean_ctor_get(x_188, 0);
x_198 = lean_ctor_get(x_188, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_188);
x_199 = lean_ctor_get(x_186, 0);
lean_inc(x_199);
x_200 = lean_ctor_get_uint8(x_186, sizeof(void*)*2);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_201 = x_186;
} else {
 lean_dec_ref(x_186);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(0, 2, 1);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_197);
lean_ctor_set_uint8(x_202, sizeof(void*)*2, x_200);
lean_ctor_set(x_182, 1, x_202);
lean_ctor_set(x_182, 0, x_1);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_182);
lean_ctor_set(x_203, 1, x_198);
return x_203;
}
}
else
{
lean_object* x_204; lean_object* x_205; uint64_t x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_204 = lean_ctor_get(x_182, 0);
x_205 = lean_ctor_get(x_182, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_182);
x_206 = lean_unbox_uint64(x_204);
lean_dec(x_204);
lean_inc(x_1);
x_207 = l_Lake_computeArtifactTrace(x_1, x_1, x_206, x_183);
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_210 = x_207;
} else {
 lean_dec_ref(x_207);
 x_210 = lean_box(0);
}
x_211 = lean_ctor_get(x_205, 0);
lean_inc(x_211);
x_212 = lean_ctor_get_uint8(x_205, sizeof(void*)*2);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_213 = x_205;
} else {
 lean_dec_ref(x_205);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(0, 2, 1);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_211);
lean_ctor_set(x_214, 1, x_208);
lean_ctor_set_uint8(x_214, sizeof(void*)*2, x_212);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_1);
lean_ctor_set(x_215, 1, x_214);
if (lean_is_scalar(x_210)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_210;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_209);
return x_216;
}
}
else
{
uint8_t x_217; 
lean_dec(x_1);
x_217 = !lean_is_exclusive(x_181);
if (x_217 == 0)
{
lean_object* x_218; uint8_t x_219; 
x_218 = lean_ctor_get(x_181, 0);
lean_dec(x_218);
x_219 = !lean_is_exclusive(x_182);
if (x_219 == 0)
{
return x_181;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_182, 0);
x_221 = lean_ctor_get(x_182, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_182);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
lean_ctor_set(x_181, 0, x_222);
return x_181;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_223 = lean_ctor_get(x_181, 1);
lean_inc(x_223);
lean_dec(x_181);
x_224 = lean_ctor_get(x_182, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_182, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_226 = x_182;
} else {
 lean_dec_ref(x_182);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(1, 2, 0);
} else {
 x_227 = x_226;
}
lean_ctor_set(x_227, 0, x_224);
lean_ctor_set(x_227, 1, x_225);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_223);
return x_228;
}
}
}
}
}
else
{
lean_object* x_538; uint8_t x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_630; 
x_538 = lean_ctor_get(x_11, 0);
x_539 = lean_ctor_get_uint8(x_11, sizeof(void*)*2);
x_540 = lean_ctor_get(x_11, 1);
lean_inc(x_540);
lean_inc(x_538);
lean_dec(x_11);
x_541 = l_Lake_buildFileUnlessUpToDate_x27___closed__0;
lean_inc(x_1);
x_542 = lean_string_append(x_1, x_541);
lean_inc(x_542);
x_543 = l_Lake_readTraceFile(x_542, x_538, x_12);
x_544 = lean_ctor_get(x_543, 0);
lean_inc(x_544);
x_545 = lean_ctor_get(x_543, 1);
lean_inc(x_545);
lean_dec(x_543);
x_546 = lean_ctor_get(x_544, 0);
lean_inc(x_546);
x_547 = lean_ctor_get(x_544, 1);
lean_inc(x_547);
if (lean_is_exclusive(x_544)) {
 lean_ctor_release(x_544, 0);
 lean_ctor_release(x_544, 1);
 x_548 = x_544;
} else {
 lean_dec_ref(x_544);
 x_548 = lean_box(0);
}
lean_inc(x_540);
x_630 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_630, 0, x_547);
lean_ctor_set(x_630, 1, x_540);
lean_ctor_set_uint8(x_630, sizeof(void*)*2, x_539);
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_548);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_4);
x_549 = x_6;
x_550 = x_7;
x_551 = x_8;
x_552 = x_9;
x_553 = x_10;
x_554 = x_630;
x_555 = x_545;
goto block_629;
}
else
{
lean_object* x_631; lean_object* x_632; 
x_631 = lean_ctor_get(x_7, 0);
lean_inc(x_631);
x_632 = lean_ctor_get(x_631, 19);
lean_inc(x_632);
lean_dec(x_631);
if (lean_obj_tag(x_632) == 0)
{
lean_dec(x_548);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_4);
x_549 = x_6;
x_550 = x_7;
x_551 = x_8;
x_552 = x_9;
x_553 = x_10;
x_554 = x_630;
x_555 = x_545;
goto block_629;
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; uint64_t x_681; lean_object* x_682; lean_object* x_683; 
x_633 = lean_ctor_get(x_632, 0);
lean_inc(x_633);
lean_dec(x_632);
x_634 = lean_ctor_get(x_540, 2);
lean_inc(x_634);
x_635 = lean_ctor_get(x_540, 3);
lean_inc(x_635);
x_676 = l_Lake_instMonadWorkspaceJobM;
x_677 = l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___redArg(x_676, x_51);
x_678 = l_Lake_buildArtifactUnlessUpToDate___closed__11;
x_679 = l_Lake_buildArtifactUnlessUpToDate___closed__12;
lean_inc(x_4);
x_680 = l_Lake_instResolveArtifactsFileOutputHashArtifactOfMonadLakeEnvOfMonadLiftTBaseIOOfMonad___redArg(x_4, x_677, x_678, x_52);
x_681 = lean_unbox_uint64(x_634);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_546);
lean_inc(x_6);
x_682 = l_Lake_resolveArtifactsUsing_x3f___at___Lake_buildArtifactUnlessUpToDate_spec__0(x_679, x_680, x_6, x_681, x_546, x_633, x_7, x_8, x_9, x_10, x_630, x_545);
x_683 = lean_ctor_get(x_682, 0);
lean_inc(x_683);
if (lean_obj_tag(x_683) == 0)
{
lean_object* x_684; 
x_684 = lean_ctor_get(x_683, 0);
lean_inc(x_684);
if (lean_obj_tag(x_684) == 0)
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; uint8_t x_690; 
x_685 = lean_ctor_get(x_682, 1);
lean_inc(x_685);
lean_dec(x_682);
x_686 = lean_ctor_get(x_683, 1);
lean_inc(x_686);
lean_dec(x_683);
x_687 = l_Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0(x_6, x_1, x_540, x_546, x_635, x_7, x_8, x_9, x_10, x_686, x_685);
lean_dec(x_635);
x_688 = lean_ctor_get(x_687, 0);
lean_inc(x_688);
x_689 = lean_ctor_get(x_688, 0);
lean_inc(x_689);
x_690 = lean_unbox(x_689);
lean_dec(x_689);
if (x_690 == 0)
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; 
x_691 = lean_ctor_get(x_687, 1);
lean_inc(x_691);
lean_dec(x_687);
x_692 = lean_ctor_get(x_688, 1);
lean_inc(x_692);
lean_dec(x_688);
lean_inc(x_10);
lean_inc(x_1);
x_693 = l_Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_3, x_540, x_542, x_6, x_7, x_8, x_9, x_10, x_692, x_691);
lean_dec(x_542);
x_694 = lean_ctor_get(x_693, 0);
lean_inc(x_694);
if (lean_obj_tag(x_694) == 0)
{
lean_object* x_695; lean_object* x_696; 
x_695 = lean_ctor_get(x_693, 1);
lean_inc(x_695);
lean_dec(x_693);
x_696 = lean_ctor_get(x_694, 1);
lean_inc(x_696);
lean_dec(x_694);
x_636 = x_10;
x_637 = x_696;
x_638 = x_695;
goto block_675;
}
else
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; 
lean_dec(x_634);
lean_dec(x_633);
lean_dec(x_548);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_1);
x_697 = lean_ctor_get(x_693, 1);
lean_inc(x_697);
if (lean_is_exclusive(x_693)) {
 lean_ctor_release(x_693, 0);
 lean_ctor_release(x_693, 1);
 x_698 = x_693;
} else {
 lean_dec_ref(x_693);
 x_698 = lean_box(0);
}
x_699 = lean_ctor_get(x_694, 0);
lean_inc(x_699);
x_700 = lean_ctor_get(x_694, 1);
lean_inc(x_700);
if (lean_is_exclusive(x_694)) {
 lean_ctor_release(x_694, 0);
 lean_ctor_release(x_694, 1);
 x_701 = x_694;
} else {
 lean_dec_ref(x_694);
 x_701 = lean_box(0);
}
if (lean_is_scalar(x_701)) {
 x_702 = lean_alloc_ctor(1, 2, 0);
} else {
 x_702 = x_701;
}
lean_ctor_set(x_702, 0, x_699);
lean_ctor_set(x_702, 1, x_700);
if (lean_is_scalar(x_698)) {
 x_703 = lean_alloc_ctor(0, 2, 0);
} else {
 x_703 = x_698;
}
lean_ctor_set(x_703, 0, x_702);
lean_ctor_set(x_703, 1, x_697);
return x_703;
}
}
else
{
lean_object* x_704; lean_object* x_705; 
lean_dec(x_542);
lean_dec(x_540);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_704 = lean_ctor_get(x_687, 1);
lean_inc(x_704);
lean_dec(x_687);
x_705 = lean_ctor_get(x_688, 1);
lean_inc(x_705);
lean_dec(x_688);
x_636 = x_10;
x_637 = x_705;
x_638 = x_704;
goto block_675;
}
}
else
{
lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_723; 
lean_dec(x_635);
lean_dec(x_634);
lean_dec(x_633);
lean_dec(x_548);
lean_dec(x_542);
lean_dec(x_540);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_706 = lean_ctor_get(x_682, 1);
lean_inc(x_706);
lean_dec(x_682);
x_707 = lean_ctor_get(x_683, 1);
lean_inc(x_707);
if (lean_is_exclusive(x_683)) {
 lean_ctor_release(x_683, 0);
 lean_ctor_release(x_683, 1);
 x_708 = x_683;
} else {
 lean_dec_ref(x_683);
 x_708 = lean_box(0);
}
x_709 = lean_ctor_get(x_684, 0);
lean_inc(x_709);
lean_dec(x_684);
x_723 = l_System_FilePath_pathExists(x_1, x_706);
if (x_5 == 0)
{
lean_object* x_724; 
lean_dec(x_708);
x_724 = lean_ctor_get(x_723, 1);
lean_inc(x_724);
lean_dec(x_723);
x_710 = x_707;
x_711 = x_724;
goto block_722;
}
else
{
lean_object* x_725; uint8_t x_726; 
x_725 = lean_ctor_get(x_723, 0);
lean_inc(x_725);
x_726 = lean_unbox(x_725);
lean_dec(x_725);
if (x_726 == 0)
{
lean_object* x_727; lean_object* x_728; uint8_t x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; uint8_t x_738; lean_object* x_739; lean_object* x_740; 
x_727 = lean_ctor_get(x_723, 1);
lean_inc(x_727);
lean_dec(x_723);
x_728 = lean_ctor_get(x_707, 0);
lean_inc(x_728);
x_729 = lean_ctor_get_uint8(x_707, sizeof(void*)*2);
x_730 = lean_ctor_get(x_707, 1);
lean_inc(x_730);
if (lean_is_exclusive(x_707)) {
 lean_ctor_release(x_707, 0);
 lean_ctor_release(x_707, 1);
 x_731 = x_707;
} else {
 lean_dec_ref(x_707);
 x_731 = lean_box(0);
}
x_732 = lean_ctor_get(x_709, 0);
lean_inc(x_732);
x_733 = lean_ctor_get(x_709, 3);
lean_inc(x_733);
x_734 = l_Lake_buildArtifactUnlessUpToDate___closed__13;
x_735 = lean_string_append(x_734, x_1);
x_736 = lean_box(0);
x_737 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_737, 0, x_735);
x_738 = lean_unbox(x_736);
lean_ctor_set_uint8(x_737, sizeof(void*)*1, x_738);
x_739 = lean_array_push(x_728, x_737);
x_740 = l_Lake_copyFile(x_732, x_1, x_727);
lean_dec(x_732);
if (lean_obj_tag(x_740) == 0)
{
lean_object* x_741; uint64_t x_742; lean_object* x_743; 
x_741 = lean_ctor_get(x_740, 1);
lean_inc(x_741);
lean_dec(x_740);
x_742 = lean_unbox_uint64(x_733);
lean_dec(x_733);
lean_inc(x_1);
x_743 = l_Lake_writeFileHash(x_1, x_742, x_741);
if (lean_obj_tag(x_743) == 0)
{
lean_object* x_744; lean_object* x_745; 
lean_dec(x_708);
x_744 = lean_ctor_get(x_743, 1);
lean_inc(x_744);
lean_dec(x_743);
if (lean_is_scalar(x_731)) {
 x_745 = lean_alloc_ctor(0, 2, 1);
} else {
 x_745 = x_731;
}
lean_ctor_set(x_745, 0, x_739);
lean_ctor_set(x_745, 1, x_730);
lean_ctor_set_uint8(x_745, sizeof(void*)*2, x_729);
x_710 = x_745;
x_711 = x_744;
goto block_722;
}
else
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; uint8_t x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; 
lean_dec(x_709);
lean_dec(x_546);
lean_dec(x_1);
x_746 = lean_ctor_get(x_743, 0);
lean_inc(x_746);
x_747 = lean_ctor_get(x_743, 1);
lean_inc(x_747);
if (lean_is_exclusive(x_743)) {
 lean_ctor_release(x_743, 0);
 lean_ctor_release(x_743, 1);
 x_748 = x_743;
} else {
 lean_dec_ref(x_743);
 x_748 = lean_box(0);
}
x_749 = lean_io_error_to_string(x_746);
x_750 = lean_box(3);
x_751 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_751, 0, x_749);
x_752 = lean_unbox(x_750);
lean_ctor_set_uint8(x_751, sizeof(void*)*1, x_752);
x_753 = lean_array_get_size(x_739);
x_754 = lean_array_push(x_739, x_751);
if (lean_is_scalar(x_731)) {
 x_755 = lean_alloc_ctor(0, 2, 1);
} else {
 x_755 = x_731;
}
lean_ctor_set(x_755, 0, x_754);
lean_ctor_set(x_755, 1, x_730);
lean_ctor_set_uint8(x_755, sizeof(void*)*2, x_729);
if (lean_is_scalar(x_708)) {
 x_756 = lean_alloc_ctor(1, 2, 0);
} else {
 x_756 = x_708;
 lean_ctor_set_tag(x_756, 1);
}
lean_ctor_set(x_756, 0, x_753);
lean_ctor_set(x_756, 1, x_755);
if (lean_is_scalar(x_748)) {
 x_757 = lean_alloc_ctor(0, 2, 0);
} else {
 x_757 = x_748;
 lean_ctor_set_tag(x_757, 0);
}
lean_ctor_set(x_757, 0, x_756);
lean_ctor_set(x_757, 1, x_747);
return x_757;
}
}
else
{
lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; uint8_t x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; 
lean_dec(x_733);
lean_dec(x_709);
lean_dec(x_546);
lean_dec(x_1);
x_758 = lean_ctor_get(x_740, 0);
lean_inc(x_758);
x_759 = lean_ctor_get(x_740, 1);
lean_inc(x_759);
if (lean_is_exclusive(x_740)) {
 lean_ctor_release(x_740, 0);
 lean_ctor_release(x_740, 1);
 x_760 = x_740;
} else {
 lean_dec_ref(x_740);
 x_760 = lean_box(0);
}
x_761 = lean_io_error_to_string(x_758);
x_762 = lean_box(3);
x_763 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_763, 0, x_761);
x_764 = lean_unbox(x_762);
lean_ctor_set_uint8(x_763, sizeof(void*)*1, x_764);
x_765 = lean_array_get_size(x_739);
x_766 = lean_array_push(x_739, x_763);
if (lean_is_scalar(x_731)) {
 x_767 = lean_alloc_ctor(0, 2, 1);
} else {
 x_767 = x_731;
}
lean_ctor_set(x_767, 0, x_766);
lean_ctor_set(x_767, 1, x_730);
lean_ctor_set_uint8(x_767, sizeof(void*)*2, x_729);
if (lean_is_scalar(x_708)) {
 x_768 = lean_alloc_ctor(1, 2, 0);
} else {
 x_768 = x_708;
 lean_ctor_set_tag(x_768, 1);
}
lean_ctor_set(x_768, 0, x_765);
lean_ctor_set(x_768, 1, x_767);
if (lean_is_scalar(x_760)) {
 x_769 = lean_alloc_ctor(0, 2, 0);
} else {
 x_769 = x_760;
 lean_ctor_set_tag(x_769, 0);
}
lean_ctor_set(x_769, 0, x_768);
lean_ctor_set(x_769, 1, x_759);
return x_769;
}
}
else
{
lean_object* x_770; 
lean_dec(x_708);
x_770 = lean_ctor_get(x_723, 1);
lean_inc(x_770);
lean_dec(x_723);
x_710 = x_707;
x_711 = x_770;
goto block_722;
}
}
block_722:
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; uint8_t x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; 
x_712 = l_Lake_SavedTrace_replayIfExists___redArg(x_546, x_710, x_711);
lean_dec(x_546);
x_713 = lean_ctor_get(x_712, 0);
lean_inc(x_713);
x_714 = lean_ctor_get(x_713, 1);
lean_inc(x_714);
lean_dec(x_713);
x_715 = lean_ctor_get(x_712, 1);
lean_inc(x_715);
lean_dec(x_712);
x_716 = lean_ctor_get(x_714, 0);
lean_inc(x_716);
x_717 = lean_ctor_get_uint8(x_714, sizeof(void*)*2);
if (lean_is_exclusive(x_714)) {
 lean_ctor_release(x_714, 0);
 lean_ctor_release(x_714, 1);
 x_718 = x_714;
} else {
 lean_dec_ref(x_714);
 x_718 = lean_box(0);
}
lean_inc(x_709);
x_719 = l_Lake_Artifact_trace(x_709);
if (lean_is_scalar(x_718)) {
 x_720 = lean_alloc_ctor(0, 2, 1);
} else {
 x_720 = x_718;
}
lean_ctor_set(x_720, 0, x_716);
lean_ctor_set(x_720, 1, x_719);
lean_ctor_set_uint8(x_720, sizeof(void*)*2, x_717);
if (x_5 == 0)
{
lean_object* x_721; 
lean_dec(x_1);
x_721 = lean_ctor_get(x_709, 0);
lean_inc(x_721);
lean_dec(x_709);
x_13 = x_715;
x_14 = x_720;
x_15 = x_721;
goto block_18;
}
else
{
lean_dec(x_709);
x_13 = x_715;
x_14 = x_720;
x_15 = x_1;
goto block_18;
}
}
}
}
else
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; 
lean_dec(x_635);
lean_dec(x_634);
lean_dec(x_633);
lean_dec(x_548);
lean_dec(x_546);
lean_dec(x_542);
lean_dec(x_540);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_771 = lean_ctor_get(x_682, 1);
lean_inc(x_771);
if (lean_is_exclusive(x_682)) {
 lean_ctor_release(x_682, 0);
 lean_ctor_release(x_682, 1);
 x_772 = x_682;
} else {
 lean_dec_ref(x_682);
 x_772 = lean_box(0);
}
x_773 = lean_ctor_get(x_683, 0);
lean_inc(x_773);
x_774 = lean_ctor_get(x_683, 1);
lean_inc(x_774);
if (lean_is_exclusive(x_683)) {
 lean_ctor_release(x_683, 0);
 lean_ctor_release(x_683, 1);
 x_775 = x_683;
} else {
 lean_dec_ref(x_683);
 x_775 = lean_box(0);
}
if (lean_is_scalar(x_775)) {
 x_776 = lean_alloc_ctor(1, 2, 0);
} else {
 x_776 = x_775;
}
lean_ctor_set(x_776, 0, x_773);
lean_ctor_set(x_776, 1, x_774);
if (lean_is_scalar(x_772)) {
 x_777 = lean_alloc_ctor(0, 2, 0);
} else {
 x_777 = x_772;
}
lean_ctor_set(x_777, 0, x_776);
lean_ctor_set(x_777, 1, x_771);
return x_777;
}
block_675:
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; uint8_t x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; 
x_639 = lean_ctor_get(x_636, 1);
lean_inc(x_639);
lean_dec(x_636);
x_640 = lean_ctor_get(x_639, 1);
lean_inc(x_640);
lean_dec(x_639);
x_641 = lean_ctor_get(x_637, 0);
lean_inc(x_641);
x_642 = lean_ctor_get_uint8(x_637, sizeof(void*)*2);
x_643 = lean_ctor_get(x_637, 1);
lean_inc(x_643);
if (lean_is_exclusive(x_637)) {
 lean_ctor_release(x_637, 0);
 lean_ctor_release(x_637, 1);
 x_644 = x_637;
} else {
 lean_dec_ref(x_637);
 x_644 = lean_box(0);
}
x_645 = lean_ctor_get(x_640, 6);
lean_inc(x_645);
lean_dec(x_640);
lean_inc(x_1);
x_646 = l_Lake_Cache_saveArtifact(x_645, x_1, x_4, x_3, x_638);
lean_dec(x_4);
if (lean_obj_tag(x_646) == 0)
{
lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; uint64_t x_654; lean_object* x_655; lean_object* x_656; uint64_t x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; 
lean_dec(x_643);
lean_dec(x_548);
x_647 = lean_ctor_get(x_646, 0);
lean_inc(x_647);
x_648 = lean_ctor_get(x_646, 1);
lean_inc(x_648);
lean_dec(x_646);
x_649 = lean_st_ref_take(x_633, x_648);
x_650 = lean_ctor_get(x_649, 0);
lean_inc(x_650);
x_651 = lean_ctor_get(x_649, 1);
lean_inc(x_651);
lean_dec(x_649);
x_652 = lean_ctor_get(x_647, 0);
lean_inc(x_652);
x_653 = lean_ctor_get(x_647, 3);
lean_inc(x_653);
x_654 = lean_unbox_uint64(x_653);
lean_dec(x_653);
x_655 = lean_uint64_to_nat(x_654);
x_656 = l_Lean_bignumToJson(x_655);
x_657 = lean_unbox_uint64(x_634);
lean_dec(x_634);
x_658 = l_Lake_CacheMap_insertCore(x_657, x_656, x_650);
x_659 = lean_st_ref_set(x_633, x_658, x_651);
lean_dec(x_633);
x_660 = lean_ctor_get(x_659, 1);
lean_inc(x_660);
lean_dec(x_659);
x_661 = l_Lake_Artifact_trace(x_647);
if (lean_is_scalar(x_644)) {
 x_662 = lean_alloc_ctor(0, 2, 1);
} else {
 x_662 = x_644;
}
lean_ctor_set(x_662, 0, x_641);
lean_ctor_set(x_662, 1, x_661);
lean_ctor_set_uint8(x_662, sizeof(void*)*2, x_642);
if (x_5 == 0)
{
lean_dec(x_1);
x_19 = x_660;
x_20 = x_662;
x_21 = x_652;
goto block_24;
}
else
{
lean_dec(x_652);
x_19 = x_660;
x_20 = x_662;
x_21 = x_1;
goto block_24;
}
}
else
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; uint8_t x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; 
lean_dec(x_634);
lean_dec(x_633);
lean_dec(x_1);
x_663 = lean_ctor_get(x_646, 0);
lean_inc(x_663);
x_664 = lean_ctor_get(x_646, 1);
lean_inc(x_664);
if (lean_is_exclusive(x_646)) {
 lean_ctor_release(x_646, 0);
 lean_ctor_release(x_646, 1);
 x_665 = x_646;
} else {
 lean_dec_ref(x_646);
 x_665 = lean_box(0);
}
x_666 = lean_io_error_to_string(x_663);
x_667 = lean_box(3);
x_668 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_668, 0, x_666);
x_669 = lean_unbox(x_667);
lean_ctor_set_uint8(x_668, sizeof(void*)*1, x_669);
x_670 = lean_array_get_size(x_641);
x_671 = lean_array_push(x_641, x_668);
if (lean_is_scalar(x_644)) {
 x_672 = lean_alloc_ctor(0, 2, 1);
} else {
 x_672 = x_644;
}
lean_ctor_set(x_672, 0, x_671);
lean_ctor_set(x_672, 1, x_643);
lean_ctor_set_uint8(x_672, sizeof(void*)*2, x_642);
if (lean_is_scalar(x_548)) {
 x_673 = lean_alloc_ctor(1, 2, 0);
} else {
 x_673 = x_548;
 lean_ctor_set_tag(x_673, 1);
}
lean_ctor_set(x_673, 0, x_670);
lean_ctor_set(x_673, 1, x_672);
if (lean_is_scalar(x_665)) {
 x_674 = lean_alloc_ctor(0, 2, 0);
} else {
 x_674 = x_665;
 lean_ctor_set_tag(x_674, 0);
}
lean_ctor_set(x_674, 0, x_673);
lean_ctor_set(x_674, 1, x_664);
return x_674;
}
}
}
}
block_629:
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; uint8_t x_560; 
x_556 = lean_ctor_get(x_540, 3);
lean_inc(x_556);
x_557 = l_Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0(x_549, x_1, x_540, x_546, x_556, x_550, x_551, x_552, x_553, x_554, x_555);
lean_dec(x_556);
x_558 = lean_ctor_get(x_557, 0);
lean_inc(x_558);
x_559 = lean_ctor_get(x_558, 0);
lean_inc(x_559);
x_560 = lean_unbox(x_559);
lean_dec(x_559);
if (x_560 == 0)
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; 
x_561 = lean_ctor_get(x_557, 1);
lean_inc(x_561);
lean_dec(x_557);
x_562 = lean_ctor_get(x_558, 1);
lean_inc(x_562);
lean_dec(x_558);
lean_inc(x_1);
x_563 = l_Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_3, x_540, x_542, x_549, x_550, x_551, x_552, x_553, x_562, x_561);
lean_dec(x_542);
x_564 = lean_ctor_get(x_563, 0);
lean_inc(x_564);
if (lean_obj_tag(x_564) == 0)
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; uint8_t x_570; lean_object* x_571; lean_object* x_572; uint64_t x_573; lean_object* x_574; 
x_565 = lean_ctor_get(x_564, 1);
lean_inc(x_565);
x_566 = lean_ctor_get(x_563, 1);
lean_inc(x_566);
lean_dec(x_563);
x_567 = lean_ctor_get(x_564, 0);
lean_inc(x_567);
if (lean_is_exclusive(x_564)) {
 lean_ctor_release(x_564, 0);
 lean_ctor_release(x_564, 1);
 x_568 = x_564;
} else {
 lean_dec_ref(x_564);
 x_568 = lean_box(0);
}
x_569 = lean_ctor_get(x_565, 0);
lean_inc(x_569);
x_570 = lean_ctor_get_uint8(x_565, sizeof(void*)*2);
x_571 = lean_ctor_get(x_565, 1);
lean_inc(x_571);
if (lean_is_exclusive(x_565)) {
 lean_ctor_release(x_565, 0);
 lean_ctor_release(x_565, 1);
 x_572 = x_565;
} else {
 lean_dec_ref(x_565);
 x_572 = lean_box(0);
}
x_573 = lean_unbox_uint64(x_567);
lean_inc(x_1);
x_574 = l_Lake_writeFileHash(x_1, x_573, x_566);
if (lean_obj_tag(x_574) == 0)
{
lean_object* x_575; uint64_t x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; 
lean_dec(x_571);
x_575 = lean_ctor_get(x_574, 1);
lean_inc(x_575);
lean_dec(x_574);
x_576 = lean_unbox_uint64(x_567);
lean_dec(x_567);
lean_inc(x_1);
x_577 = l_Lake_computeArtifactTrace(x_1, x_1, x_576, x_575);
x_578 = lean_ctor_get(x_577, 0);
lean_inc(x_578);
x_579 = lean_ctor_get(x_577, 1);
lean_inc(x_579);
if (lean_is_exclusive(x_577)) {
 lean_ctor_release(x_577, 0);
 lean_ctor_release(x_577, 1);
 x_580 = x_577;
} else {
 lean_dec_ref(x_577);
 x_580 = lean_box(0);
}
if (lean_is_scalar(x_572)) {
 x_581 = lean_alloc_ctor(0, 2, 1);
} else {
 x_581 = x_572;
}
lean_ctor_set(x_581, 0, x_569);
lean_ctor_set(x_581, 1, x_578);
lean_ctor_set_uint8(x_581, sizeof(void*)*2, x_570);
if (lean_is_scalar(x_568)) {
 x_582 = lean_alloc_ctor(0, 2, 0);
} else {
 x_582 = x_568;
}
lean_ctor_set(x_582, 0, x_1);
lean_ctor_set(x_582, 1, x_581);
if (lean_is_scalar(x_580)) {
 x_583 = lean_alloc_ctor(0, 2, 0);
} else {
 x_583 = x_580;
}
lean_ctor_set(x_583, 0, x_582);
lean_ctor_set(x_583, 1, x_579);
return x_583;
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; uint8_t x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; 
lean_dec(x_567);
lean_dec(x_1);
x_584 = lean_ctor_get(x_574, 0);
lean_inc(x_584);
x_585 = lean_ctor_get(x_574, 1);
lean_inc(x_585);
if (lean_is_exclusive(x_574)) {
 lean_ctor_release(x_574, 0);
 lean_ctor_release(x_574, 1);
 x_586 = x_574;
} else {
 lean_dec_ref(x_574);
 x_586 = lean_box(0);
}
x_587 = lean_io_error_to_string(x_584);
x_588 = lean_box(3);
x_589 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_589, 0, x_587);
x_590 = lean_unbox(x_588);
lean_ctor_set_uint8(x_589, sizeof(void*)*1, x_590);
x_591 = lean_array_get_size(x_569);
x_592 = lean_array_push(x_569, x_589);
if (lean_is_scalar(x_572)) {
 x_593 = lean_alloc_ctor(0, 2, 1);
} else {
 x_593 = x_572;
}
lean_ctor_set(x_593, 0, x_592);
lean_ctor_set(x_593, 1, x_571);
lean_ctor_set_uint8(x_593, sizeof(void*)*2, x_570);
if (lean_is_scalar(x_568)) {
 x_594 = lean_alloc_ctor(1, 2, 0);
} else {
 x_594 = x_568;
 lean_ctor_set_tag(x_594, 1);
}
lean_ctor_set(x_594, 0, x_591);
lean_ctor_set(x_594, 1, x_593);
if (lean_is_scalar(x_586)) {
 x_595 = lean_alloc_ctor(0, 2, 0);
} else {
 x_595 = x_586;
 lean_ctor_set_tag(x_595, 0);
}
lean_ctor_set(x_595, 0, x_594);
lean_ctor_set(x_595, 1, x_585);
return x_595;
}
}
else
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; 
lean_dec(x_1);
x_596 = lean_ctor_get(x_563, 1);
lean_inc(x_596);
if (lean_is_exclusive(x_563)) {
 lean_ctor_release(x_563, 0);
 lean_ctor_release(x_563, 1);
 x_597 = x_563;
} else {
 lean_dec_ref(x_563);
 x_597 = lean_box(0);
}
x_598 = lean_ctor_get(x_564, 0);
lean_inc(x_598);
x_599 = lean_ctor_get(x_564, 1);
lean_inc(x_599);
if (lean_is_exclusive(x_564)) {
 lean_ctor_release(x_564, 0);
 lean_ctor_release(x_564, 1);
 x_600 = x_564;
} else {
 lean_dec_ref(x_564);
 x_600 = lean_box(0);
}
if (lean_is_scalar(x_600)) {
 x_601 = lean_alloc_ctor(1, 2, 0);
} else {
 x_601 = x_600;
}
lean_ctor_set(x_601, 0, x_598);
lean_ctor_set(x_601, 1, x_599);
if (lean_is_scalar(x_597)) {
 x_602 = lean_alloc_ctor(0, 2, 0);
} else {
 x_602 = x_597;
}
lean_ctor_set(x_602, 0, x_601);
lean_ctor_set(x_602, 1, x_596);
return x_602;
}
}
else
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; 
lean_dec(x_552);
lean_dec(x_551);
lean_dec(x_550);
lean_dec(x_549);
lean_dec(x_542);
lean_dec(x_540);
lean_dec(x_2);
x_603 = lean_ctor_get(x_557, 1);
lean_inc(x_603);
lean_dec(x_557);
x_604 = lean_ctor_get(x_558, 1);
lean_inc(x_604);
lean_dec(x_558);
lean_inc(x_1);
x_605 = l_Lake_fetchFileHash___redArg(x_1, x_3, x_553, x_604, x_603);
lean_dec(x_553);
x_606 = lean_ctor_get(x_605, 0);
lean_inc(x_606);
if (lean_obj_tag(x_606) == 0)
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; uint64_t x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; uint8_t x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; 
x_607 = lean_ctor_get(x_605, 1);
lean_inc(x_607);
lean_dec(x_605);
x_608 = lean_ctor_get(x_606, 0);
lean_inc(x_608);
x_609 = lean_ctor_get(x_606, 1);
lean_inc(x_609);
if (lean_is_exclusive(x_606)) {
 lean_ctor_release(x_606, 0);
 lean_ctor_release(x_606, 1);
 x_610 = x_606;
} else {
 lean_dec_ref(x_606);
 x_610 = lean_box(0);
}
x_611 = lean_unbox_uint64(x_608);
lean_dec(x_608);
lean_inc(x_1);
x_612 = l_Lake_computeArtifactTrace(x_1, x_1, x_611, x_607);
x_613 = lean_ctor_get(x_612, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_612, 1);
lean_inc(x_614);
if (lean_is_exclusive(x_612)) {
 lean_ctor_release(x_612, 0);
 lean_ctor_release(x_612, 1);
 x_615 = x_612;
} else {
 lean_dec_ref(x_612);
 x_615 = lean_box(0);
}
x_616 = lean_ctor_get(x_609, 0);
lean_inc(x_616);
x_617 = lean_ctor_get_uint8(x_609, sizeof(void*)*2);
if (lean_is_exclusive(x_609)) {
 lean_ctor_release(x_609, 0);
 lean_ctor_release(x_609, 1);
 x_618 = x_609;
} else {
 lean_dec_ref(x_609);
 x_618 = lean_box(0);
}
if (lean_is_scalar(x_618)) {
 x_619 = lean_alloc_ctor(0, 2, 1);
} else {
 x_619 = x_618;
}
lean_ctor_set(x_619, 0, x_616);
lean_ctor_set(x_619, 1, x_613);
lean_ctor_set_uint8(x_619, sizeof(void*)*2, x_617);
if (lean_is_scalar(x_610)) {
 x_620 = lean_alloc_ctor(0, 2, 0);
} else {
 x_620 = x_610;
}
lean_ctor_set(x_620, 0, x_1);
lean_ctor_set(x_620, 1, x_619);
if (lean_is_scalar(x_615)) {
 x_621 = lean_alloc_ctor(0, 2, 0);
} else {
 x_621 = x_615;
}
lean_ctor_set(x_621, 0, x_620);
lean_ctor_set(x_621, 1, x_614);
return x_621;
}
else
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; 
lean_dec(x_1);
x_622 = lean_ctor_get(x_605, 1);
lean_inc(x_622);
if (lean_is_exclusive(x_605)) {
 lean_ctor_release(x_605, 0);
 lean_ctor_release(x_605, 1);
 x_623 = x_605;
} else {
 lean_dec_ref(x_605);
 x_623 = lean_box(0);
}
x_624 = lean_ctor_get(x_606, 0);
lean_inc(x_624);
x_625 = lean_ctor_get(x_606, 1);
lean_inc(x_625);
if (lean_is_exclusive(x_606)) {
 lean_ctor_release(x_606, 0);
 lean_ctor_release(x_606, 1);
 x_626 = x_606;
} else {
 lean_dec_ref(x_606);
 x_626 = lean_box(0);
}
if (lean_is_scalar(x_626)) {
 x_627 = lean_alloc_ctor(1, 2, 0);
} else {
 x_627 = x_626;
}
lean_ctor_set(x_627, 0, x_624);
lean_ctor_set(x_627, 1, x_625);
if (lean_is_scalar(x_623)) {
 x_628 = lean_alloc_ctor(0, 2, 0);
} else {
 x_628 = x_623;
}
lean_ctor_set(x_628, 0, x_627);
lean_ctor_set(x_628, 1, x_622);
return x_628;
}
}
}
}
}
else
{
lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; uint8_t x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_878; 
x_778 = lean_ctor_get(x_43, 0);
lean_inc(x_778);
lean_dec(x_43);
x_779 = lean_ctor_get(x_778, 0);
lean_inc(x_779);
lean_dec(x_778);
lean_inc(x_779);
x_780 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_780, 0, x_779);
x_781 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_781, 0, x_779);
x_782 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_782, 0, x_780);
lean_ctor_set(x_782, 1, x_781);
x_783 = l_Lake_EquipT_instFunctor___redArg(x_782);
x_784 = l_Lake_EquipT_instMonad___redArg(x_44);
x_785 = lean_ctor_get(x_11, 0);
lean_inc(x_785);
x_786 = lean_ctor_get_uint8(x_11, sizeof(void*)*2);
x_787 = lean_ctor_get(x_11, 1);
lean_inc(x_787);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_788 = x_11;
} else {
 lean_dec_ref(x_11);
 x_788 = lean_box(0);
}
x_789 = l_Lake_buildFileUnlessUpToDate_x27___closed__0;
lean_inc(x_1);
x_790 = lean_string_append(x_1, x_789);
lean_inc(x_790);
x_791 = l_Lake_readTraceFile(x_790, x_785, x_12);
x_792 = lean_ctor_get(x_791, 0);
lean_inc(x_792);
x_793 = lean_ctor_get(x_791, 1);
lean_inc(x_793);
lean_dec(x_791);
x_794 = lean_ctor_get(x_792, 0);
lean_inc(x_794);
x_795 = lean_ctor_get(x_792, 1);
lean_inc(x_795);
if (lean_is_exclusive(x_792)) {
 lean_ctor_release(x_792, 0);
 lean_ctor_release(x_792, 1);
 x_796 = x_792;
} else {
 lean_dec_ref(x_792);
 x_796 = lean_box(0);
}
lean_inc(x_787);
if (lean_is_scalar(x_788)) {
 x_878 = lean_alloc_ctor(0, 2, 1);
} else {
 x_878 = x_788;
}
lean_ctor_set(x_878, 0, x_795);
lean_ctor_set(x_878, 1, x_787);
lean_ctor_set_uint8(x_878, sizeof(void*)*2, x_786);
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_796);
lean_dec(x_784);
lean_dec(x_783);
lean_dec(x_4);
x_797 = x_6;
x_798 = x_7;
x_799 = x_8;
x_800 = x_9;
x_801 = x_10;
x_802 = x_878;
x_803 = x_793;
goto block_877;
}
else
{
lean_object* x_879; lean_object* x_880; 
x_879 = lean_ctor_get(x_7, 0);
lean_inc(x_879);
x_880 = lean_ctor_get(x_879, 19);
lean_inc(x_880);
lean_dec(x_879);
if (lean_obj_tag(x_880) == 0)
{
lean_dec(x_796);
lean_dec(x_784);
lean_dec(x_783);
lean_dec(x_4);
x_797 = x_6;
x_798 = x_7;
x_799 = x_8;
x_800 = x_9;
x_801 = x_10;
x_802 = x_878;
x_803 = x_793;
goto block_877;
}
else
{
lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; uint64_t x_929; lean_object* x_930; lean_object* x_931; 
x_881 = lean_ctor_get(x_880, 0);
lean_inc(x_881);
lean_dec(x_880);
x_882 = lean_ctor_get(x_787, 2);
lean_inc(x_882);
x_883 = lean_ctor_get(x_787, 3);
lean_inc(x_883);
x_924 = l_Lake_instMonadWorkspaceJobM;
x_925 = l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___redArg(x_924, x_783);
x_926 = l_Lake_buildArtifactUnlessUpToDate___closed__11;
x_927 = l_Lake_buildArtifactUnlessUpToDate___closed__12;
lean_inc(x_4);
x_928 = l_Lake_instResolveArtifactsFileOutputHashArtifactOfMonadLakeEnvOfMonadLiftTBaseIOOfMonad___redArg(x_4, x_925, x_926, x_784);
x_929 = lean_unbox_uint64(x_882);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_794);
lean_inc(x_6);
x_930 = l_Lake_resolveArtifactsUsing_x3f___at___Lake_buildArtifactUnlessUpToDate_spec__0(x_927, x_928, x_6, x_929, x_794, x_881, x_7, x_8, x_9, x_10, x_878, x_793);
x_931 = lean_ctor_get(x_930, 0);
lean_inc(x_931);
if (lean_obj_tag(x_931) == 0)
{
lean_object* x_932; 
x_932 = lean_ctor_get(x_931, 0);
lean_inc(x_932);
if (lean_obj_tag(x_932) == 0)
{
lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; uint8_t x_938; 
x_933 = lean_ctor_get(x_930, 1);
lean_inc(x_933);
lean_dec(x_930);
x_934 = lean_ctor_get(x_931, 1);
lean_inc(x_934);
lean_dec(x_931);
x_935 = l_Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0(x_6, x_1, x_787, x_794, x_883, x_7, x_8, x_9, x_10, x_934, x_933);
lean_dec(x_883);
x_936 = lean_ctor_get(x_935, 0);
lean_inc(x_936);
x_937 = lean_ctor_get(x_936, 0);
lean_inc(x_937);
x_938 = lean_unbox(x_937);
lean_dec(x_937);
if (x_938 == 0)
{
lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; 
x_939 = lean_ctor_get(x_935, 1);
lean_inc(x_939);
lean_dec(x_935);
x_940 = lean_ctor_get(x_936, 1);
lean_inc(x_940);
lean_dec(x_936);
lean_inc(x_10);
lean_inc(x_1);
x_941 = l_Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_3, x_787, x_790, x_6, x_7, x_8, x_9, x_10, x_940, x_939);
lean_dec(x_790);
x_942 = lean_ctor_get(x_941, 0);
lean_inc(x_942);
if (lean_obj_tag(x_942) == 0)
{
lean_object* x_943; lean_object* x_944; 
x_943 = lean_ctor_get(x_941, 1);
lean_inc(x_943);
lean_dec(x_941);
x_944 = lean_ctor_get(x_942, 1);
lean_inc(x_944);
lean_dec(x_942);
x_884 = x_10;
x_885 = x_944;
x_886 = x_943;
goto block_923;
}
else
{
lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; 
lean_dec(x_882);
lean_dec(x_881);
lean_dec(x_796);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_1);
x_945 = lean_ctor_get(x_941, 1);
lean_inc(x_945);
if (lean_is_exclusive(x_941)) {
 lean_ctor_release(x_941, 0);
 lean_ctor_release(x_941, 1);
 x_946 = x_941;
} else {
 lean_dec_ref(x_941);
 x_946 = lean_box(0);
}
x_947 = lean_ctor_get(x_942, 0);
lean_inc(x_947);
x_948 = lean_ctor_get(x_942, 1);
lean_inc(x_948);
if (lean_is_exclusive(x_942)) {
 lean_ctor_release(x_942, 0);
 lean_ctor_release(x_942, 1);
 x_949 = x_942;
} else {
 lean_dec_ref(x_942);
 x_949 = lean_box(0);
}
if (lean_is_scalar(x_949)) {
 x_950 = lean_alloc_ctor(1, 2, 0);
} else {
 x_950 = x_949;
}
lean_ctor_set(x_950, 0, x_947);
lean_ctor_set(x_950, 1, x_948);
if (lean_is_scalar(x_946)) {
 x_951 = lean_alloc_ctor(0, 2, 0);
} else {
 x_951 = x_946;
}
lean_ctor_set(x_951, 0, x_950);
lean_ctor_set(x_951, 1, x_945);
return x_951;
}
}
else
{
lean_object* x_952; lean_object* x_953; 
lean_dec(x_790);
lean_dec(x_787);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_952 = lean_ctor_get(x_935, 1);
lean_inc(x_952);
lean_dec(x_935);
x_953 = lean_ctor_get(x_936, 1);
lean_inc(x_953);
lean_dec(x_936);
x_884 = x_10;
x_885 = x_953;
x_886 = x_952;
goto block_923;
}
}
else
{
lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_971; 
lean_dec(x_883);
lean_dec(x_882);
lean_dec(x_881);
lean_dec(x_796);
lean_dec(x_790);
lean_dec(x_787);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_954 = lean_ctor_get(x_930, 1);
lean_inc(x_954);
lean_dec(x_930);
x_955 = lean_ctor_get(x_931, 1);
lean_inc(x_955);
if (lean_is_exclusive(x_931)) {
 lean_ctor_release(x_931, 0);
 lean_ctor_release(x_931, 1);
 x_956 = x_931;
} else {
 lean_dec_ref(x_931);
 x_956 = lean_box(0);
}
x_957 = lean_ctor_get(x_932, 0);
lean_inc(x_957);
lean_dec(x_932);
x_971 = l_System_FilePath_pathExists(x_1, x_954);
if (x_5 == 0)
{
lean_object* x_972; 
lean_dec(x_956);
x_972 = lean_ctor_get(x_971, 1);
lean_inc(x_972);
lean_dec(x_971);
x_958 = x_955;
x_959 = x_972;
goto block_970;
}
else
{
lean_object* x_973; uint8_t x_974; 
x_973 = lean_ctor_get(x_971, 0);
lean_inc(x_973);
x_974 = lean_unbox(x_973);
lean_dec(x_973);
if (x_974 == 0)
{
lean_object* x_975; lean_object* x_976; uint8_t x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; uint8_t x_986; lean_object* x_987; lean_object* x_988; 
x_975 = lean_ctor_get(x_971, 1);
lean_inc(x_975);
lean_dec(x_971);
x_976 = lean_ctor_get(x_955, 0);
lean_inc(x_976);
x_977 = lean_ctor_get_uint8(x_955, sizeof(void*)*2);
x_978 = lean_ctor_get(x_955, 1);
lean_inc(x_978);
if (lean_is_exclusive(x_955)) {
 lean_ctor_release(x_955, 0);
 lean_ctor_release(x_955, 1);
 x_979 = x_955;
} else {
 lean_dec_ref(x_955);
 x_979 = lean_box(0);
}
x_980 = lean_ctor_get(x_957, 0);
lean_inc(x_980);
x_981 = lean_ctor_get(x_957, 3);
lean_inc(x_981);
x_982 = l_Lake_buildArtifactUnlessUpToDate___closed__13;
x_983 = lean_string_append(x_982, x_1);
x_984 = lean_box(0);
x_985 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_985, 0, x_983);
x_986 = lean_unbox(x_984);
lean_ctor_set_uint8(x_985, sizeof(void*)*1, x_986);
x_987 = lean_array_push(x_976, x_985);
x_988 = l_Lake_copyFile(x_980, x_1, x_975);
lean_dec(x_980);
if (lean_obj_tag(x_988) == 0)
{
lean_object* x_989; uint64_t x_990; lean_object* x_991; 
x_989 = lean_ctor_get(x_988, 1);
lean_inc(x_989);
lean_dec(x_988);
x_990 = lean_unbox_uint64(x_981);
lean_dec(x_981);
lean_inc(x_1);
x_991 = l_Lake_writeFileHash(x_1, x_990, x_989);
if (lean_obj_tag(x_991) == 0)
{
lean_object* x_992; lean_object* x_993; 
lean_dec(x_956);
x_992 = lean_ctor_get(x_991, 1);
lean_inc(x_992);
lean_dec(x_991);
if (lean_is_scalar(x_979)) {
 x_993 = lean_alloc_ctor(0, 2, 1);
} else {
 x_993 = x_979;
}
lean_ctor_set(x_993, 0, x_987);
lean_ctor_set(x_993, 1, x_978);
lean_ctor_set_uint8(x_993, sizeof(void*)*2, x_977);
x_958 = x_993;
x_959 = x_992;
goto block_970;
}
else
{
lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; uint8_t x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; 
lean_dec(x_957);
lean_dec(x_794);
lean_dec(x_1);
x_994 = lean_ctor_get(x_991, 0);
lean_inc(x_994);
x_995 = lean_ctor_get(x_991, 1);
lean_inc(x_995);
if (lean_is_exclusive(x_991)) {
 lean_ctor_release(x_991, 0);
 lean_ctor_release(x_991, 1);
 x_996 = x_991;
} else {
 lean_dec_ref(x_991);
 x_996 = lean_box(0);
}
x_997 = lean_io_error_to_string(x_994);
x_998 = lean_box(3);
x_999 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_999, 0, x_997);
x_1000 = lean_unbox(x_998);
lean_ctor_set_uint8(x_999, sizeof(void*)*1, x_1000);
x_1001 = lean_array_get_size(x_987);
x_1002 = lean_array_push(x_987, x_999);
if (lean_is_scalar(x_979)) {
 x_1003 = lean_alloc_ctor(0, 2, 1);
} else {
 x_1003 = x_979;
}
lean_ctor_set(x_1003, 0, x_1002);
lean_ctor_set(x_1003, 1, x_978);
lean_ctor_set_uint8(x_1003, sizeof(void*)*2, x_977);
if (lean_is_scalar(x_956)) {
 x_1004 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1004 = x_956;
 lean_ctor_set_tag(x_1004, 1);
}
lean_ctor_set(x_1004, 0, x_1001);
lean_ctor_set(x_1004, 1, x_1003);
if (lean_is_scalar(x_996)) {
 x_1005 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1005 = x_996;
 lean_ctor_set_tag(x_1005, 0);
}
lean_ctor_set(x_1005, 0, x_1004);
lean_ctor_set(x_1005, 1, x_995);
return x_1005;
}
}
else
{
lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; uint8_t x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; 
lean_dec(x_981);
lean_dec(x_957);
lean_dec(x_794);
lean_dec(x_1);
x_1006 = lean_ctor_get(x_988, 0);
lean_inc(x_1006);
x_1007 = lean_ctor_get(x_988, 1);
lean_inc(x_1007);
if (lean_is_exclusive(x_988)) {
 lean_ctor_release(x_988, 0);
 lean_ctor_release(x_988, 1);
 x_1008 = x_988;
} else {
 lean_dec_ref(x_988);
 x_1008 = lean_box(0);
}
x_1009 = lean_io_error_to_string(x_1006);
x_1010 = lean_box(3);
x_1011 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1011, 0, x_1009);
x_1012 = lean_unbox(x_1010);
lean_ctor_set_uint8(x_1011, sizeof(void*)*1, x_1012);
x_1013 = lean_array_get_size(x_987);
x_1014 = lean_array_push(x_987, x_1011);
if (lean_is_scalar(x_979)) {
 x_1015 = lean_alloc_ctor(0, 2, 1);
} else {
 x_1015 = x_979;
}
lean_ctor_set(x_1015, 0, x_1014);
lean_ctor_set(x_1015, 1, x_978);
lean_ctor_set_uint8(x_1015, sizeof(void*)*2, x_977);
if (lean_is_scalar(x_956)) {
 x_1016 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1016 = x_956;
 lean_ctor_set_tag(x_1016, 1);
}
lean_ctor_set(x_1016, 0, x_1013);
lean_ctor_set(x_1016, 1, x_1015);
if (lean_is_scalar(x_1008)) {
 x_1017 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1017 = x_1008;
 lean_ctor_set_tag(x_1017, 0);
}
lean_ctor_set(x_1017, 0, x_1016);
lean_ctor_set(x_1017, 1, x_1007);
return x_1017;
}
}
else
{
lean_object* x_1018; 
lean_dec(x_956);
x_1018 = lean_ctor_get(x_971, 1);
lean_inc(x_1018);
lean_dec(x_971);
x_958 = x_955;
x_959 = x_1018;
goto block_970;
}
}
block_970:
{
lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; uint8_t x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; 
x_960 = l_Lake_SavedTrace_replayIfExists___redArg(x_794, x_958, x_959);
lean_dec(x_794);
x_961 = lean_ctor_get(x_960, 0);
lean_inc(x_961);
x_962 = lean_ctor_get(x_961, 1);
lean_inc(x_962);
lean_dec(x_961);
x_963 = lean_ctor_get(x_960, 1);
lean_inc(x_963);
lean_dec(x_960);
x_964 = lean_ctor_get(x_962, 0);
lean_inc(x_964);
x_965 = lean_ctor_get_uint8(x_962, sizeof(void*)*2);
if (lean_is_exclusive(x_962)) {
 lean_ctor_release(x_962, 0);
 lean_ctor_release(x_962, 1);
 x_966 = x_962;
} else {
 lean_dec_ref(x_962);
 x_966 = lean_box(0);
}
lean_inc(x_957);
x_967 = l_Lake_Artifact_trace(x_957);
if (lean_is_scalar(x_966)) {
 x_968 = lean_alloc_ctor(0, 2, 1);
} else {
 x_968 = x_966;
}
lean_ctor_set(x_968, 0, x_964);
lean_ctor_set(x_968, 1, x_967);
lean_ctor_set_uint8(x_968, sizeof(void*)*2, x_965);
if (x_5 == 0)
{
lean_object* x_969; 
lean_dec(x_1);
x_969 = lean_ctor_get(x_957, 0);
lean_inc(x_969);
lean_dec(x_957);
x_13 = x_963;
x_14 = x_968;
x_15 = x_969;
goto block_18;
}
else
{
lean_dec(x_957);
x_13 = x_963;
x_14 = x_968;
x_15 = x_1;
goto block_18;
}
}
}
}
else
{
lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; 
lean_dec(x_883);
lean_dec(x_882);
lean_dec(x_881);
lean_dec(x_796);
lean_dec(x_794);
lean_dec(x_790);
lean_dec(x_787);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1019 = lean_ctor_get(x_930, 1);
lean_inc(x_1019);
if (lean_is_exclusive(x_930)) {
 lean_ctor_release(x_930, 0);
 lean_ctor_release(x_930, 1);
 x_1020 = x_930;
} else {
 lean_dec_ref(x_930);
 x_1020 = lean_box(0);
}
x_1021 = lean_ctor_get(x_931, 0);
lean_inc(x_1021);
x_1022 = lean_ctor_get(x_931, 1);
lean_inc(x_1022);
if (lean_is_exclusive(x_931)) {
 lean_ctor_release(x_931, 0);
 lean_ctor_release(x_931, 1);
 x_1023 = x_931;
} else {
 lean_dec_ref(x_931);
 x_1023 = lean_box(0);
}
if (lean_is_scalar(x_1023)) {
 x_1024 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1024 = x_1023;
}
lean_ctor_set(x_1024, 0, x_1021);
lean_ctor_set(x_1024, 1, x_1022);
if (lean_is_scalar(x_1020)) {
 x_1025 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1025 = x_1020;
}
lean_ctor_set(x_1025, 0, x_1024);
lean_ctor_set(x_1025, 1, x_1019);
return x_1025;
}
block_923:
{
lean_object* x_887; lean_object* x_888; lean_object* x_889; uint8_t x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; 
x_887 = lean_ctor_get(x_884, 1);
lean_inc(x_887);
lean_dec(x_884);
x_888 = lean_ctor_get(x_887, 1);
lean_inc(x_888);
lean_dec(x_887);
x_889 = lean_ctor_get(x_885, 0);
lean_inc(x_889);
x_890 = lean_ctor_get_uint8(x_885, sizeof(void*)*2);
x_891 = lean_ctor_get(x_885, 1);
lean_inc(x_891);
if (lean_is_exclusive(x_885)) {
 lean_ctor_release(x_885, 0);
 lean_ctor_release(x_885, 1);
 x_892 = x_885;
} else {
 lean_dec_ref(x_885);
 x_892 = lean_box(0);
}
x_893 = lean_ctor_get(x_888, 6);
lean_inc(x_893);
lean_dec(x_888);
lean_inc(x_1);
x_894 = l_Lake_Cache_saveArtifact(x_893, x_1, x_4, x_3, x_886);
lean_dec(x_4);
if (lean_obj_tag(x_894) == 0)
{
lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; uint64_t x_902; lean_object* x_903; lean_object* x_904; uint64_t x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; 
lean_dec(x_891);
lean_dec(x_796);
x_895 = lean_ctor_get(x_894, 0);
lean_inc(x_895);
x_896 = lean_ctor_get(x_894, 1);
lean_inc(x_896);
lean_dec(x_894);
x_897 = lean_st_ref_take(x_881, x_896);
x_898 = lean_ctor_get(x_897, 0);
lean_inc(x_898);
x_899 = lean_ctor_get(x_897, 1);
lean_inc(x_899);
lean_dec(x_897);
x_900 = lean_ctor_get(x_895, 0);
lean_inc(x_900);
x_901 = lean_ctor_get(x_895, 3);
lean_inc(x_901);
x_902 = lean_unbox_uint64(x_901);
lean_dec(x_901);
x_903 = lean_uint64_to_nat(x_902);
x_904 = l_Lean_bignumToJson(x_903);
x_905 = lean_unbox_uint64(x_882);
lean_dec(x_882);
x_906 = l_Lake_CacheMap_insertCore(x_905, x_904, x_898);
x_907 = lean_st_ref_set(x_881, x_906, x_899);
lean_dec(x_881);
x_908 = lean_ctor_get(x_907, 1);
lean_inc(x_908);
lean_dec(x_907);
x_909 = l_Lake_Artifact_trace(x_895);
if (lean_is_scalar(x_892)) {
 x_910 = lean_alloc_ctor(0, 2, 1);
} else {
 x_910 = x_892;
}
lean_ctor_set(x_910, 0, x_889);
lean_ctor_set(x_910, 1, x_909);
lean_ctor_set_uint8(x_910, sizeof(void*)*2, x_890);
if (x_5 == 0)
{
lean_dec(x_1);
x_19 = x_908;
x_20 = x_910;
x_21 = x_900;
goto block_24;
}
else
{
lean_dec(x_900);
x_19 = x_908;
x_20 = x_910;
x_21 = x_1;
goto block_24;
}
}
else
{
lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; uint8_t x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; 
lean_dec(x_882);
lean_dec(x_881);
lean_dec(x_1);
x_911 = lean_ctor_get(x_894, 0);
lean_inc(x_911);
x_912 = lean_ctor_get(x_894, 1);
lean_inc(x_912);
if (lean_is_exclusive(x_894)) {
 lean_ctor_release(x_894, 0);
 lean_ctor_release(x_894, 1);
 x_913 = x_894;
} else {
 lean_dec_ref(x_894);
 x_913 = lean_box(0);
}
x_914 = lean_io_error_to_string(x_911);
x_915 = lean_box(3);
x_916 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_916, 0, x_914);
x_917 = lean_unbox(x_915);
lean_ctor_set_uint8(x_916, sizeof(void*)*1, x_917);
x_918 = lean_array_get_size(x_889);
x_919 = lean_array_push(x_889, x_916);
if (lean_is_scalar(x_892)) {
 x_920 = lean_alloc_ctor(0, 2, 1);
} else {
 x_920 = x_892;
}
lean_ctor_set(x_920, 0, x_919);
lean_ctor_set(x_920, 1, x_891);
lean_ctor_set_uint8(x_920, sizeof(void*)*2, x_890);
if (lean_is_scalar(x_796)) {
 x_921 = lean_alloc_ctor(1, 2, 0);
} else {
 x_921 = x_796;
 lean_ctor_set_tag(x_921, 1);
}
lean_ctor_set(x_921, 0, x_918);
lean_ctor_set(x_921, 1, x_920);
if (lean_is_scalar(x_913)) {
 x_922 = lean_alloc_ctor(0, 2, 0);
} else {
 x_922 = x_913;
 lean_ctor_set_tag(x_922, 0);
}
lean_ctor_set(x_922, 0, x_921);
lean_ctor_set(x_922, 1, x_912);
return x_922;
}
}
}
}
block_877:
{
lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; uint8_t x_808; 
x_804 = lean_ctor_get(x_787, 3);
lean_inc(x_804);
x_805 = l_Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0(x_797, x_1, x_787, x_794, x_804, x_798, x_799, x_800, x_801, x_802, x_803);
lean_dec(x_804);
x_806 = lean_ctor_get(x_805, 0);
lean_inc(x_806);
x_807 = lean_ctor_get(x_806, 0);
lean_inc(x_807);
x_808 = lean_unbox(x_807);
lean_dec(x_807);
if (x_808 == 0)
{
lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; 
x_809 = lean_ctor_get(x_805, 1);
lean_inc(x_809);
lean_dec(x_805);
x_810 = lean_ctor_get(x_806, 1);
lean_inc(x_810);
lean_dec(x_806);
lean_inc(x_1);
x_811 = l_Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_3, x_787, x_790, x_797, x_798, x_799, x_800, x_801, x_810, x_809);
lean_dec(x_790);
x_812 = lean_ctor_get(x_811, 0);
lean_inc(x_812);
if (lean_obj_tag(x_812) == 0)
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; uint8_t x_818; lean_object* x_819; lean_object* x_820; uint64_t x_821; lean_object* x_822; 
x_813 = lean_ctor_get(x_812, 1);
lean_inc(x_813);
x_814 = lean_ctor_get(x_811, 1);
lean_inc(x_814);
lean_dec(x_811);
x_815 = lean_ctor_get(x_812, 0);
lean_inc(x_815);
if (lean_is_exclusive(x_812)) {
 lean_ctor_release(x_812, 0);
 lean_ctor_release(x_812, 1);
 x_816 = x_812;
} else {
 lean_dec_ref(x_812);
 x_816 = lean_box(0);
}
x_817 = lean_ctor_get(x_813, 0);
lean_inc(x_817);
x_818 = lean_ctor_get_uint8(x_813, sizeof(void*)*2);
x_819 = lean_ctor_get(x_813, 1);
lean_inc(x_819);
if (lean_is_exclusive(x_813)) {
 lean_ctor_release(x_813, 0);
 lean_ctor_release(x_813, 1);
 x_820 = x_813;
} else {
 lean_dec_ref(x_813);
 x_820 = lean_box(0);
}
x_821 = lean_unbox_uint64(x_815);
lean_inc(x_1);
x_822 = l_Lake_writeFileHash(x_1, x_821, x_814);
if (lean_obj_tag(x_822) == 0)
{
lean_object* x_823; uint64_t x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; 
lean_dec(x_819);
x_823 = lean_ctor_get(x_822, 1);
lean_inc(x_823);
lean_dec(x_822);
x_824 = lean_unbox_uint64(x_815);
lean_dec(x_815);
lean_inc(x_1);
x_825 = l_Lake_computeArtifactTrace(x_1, x_1, x_824, x_823);
x_826 = lean_ctor_get(x_825, 0);
lean_inc(x_826);
x_827 = lean_ctor_get(x_825, 1);
lean_inc(x_827);
if (lean_is_exclusive(x_825)) {
 lean_ctor_release(x_825, 0);
 lean_ctor_release(x_825, 1);
 x_828 = x_825;
} else {
 lean_dec_ref(x_825);
 x_828 = lean_box(0);
}
if (lean_is_scalar(x_820)) {
 x_829 = lean_alloc_ctor(0, 2, 1);
} else {
 x_829 = x_820;
}
lean_ctor_set(x_829, 0, x_817);
lean_ctor_set(x_829, 1, x_826);
lean_ctor_set_uint8(x_829, sizeof(void*)*2, x_818);
if (lean_is_scalar(x_816)) {
 x_830 = lean_alloc_ctor(0, 2, 0);
} else {
 x_830 = x_816;
}
lean_ctor_set(x_830, 0, x_1);
lean_ctor_set(x_830, 1, x_829);
if (lean_is_scalar(x_828)) {
 x_831 = lean_alloc_ctor(0, 2, 0);
} else {
 x_831 = x_828;
}
lean_ctor_set(x_831, 0, x_830);
lean_ctor_set(x_831, 1, x_827);
return x_831;
}
else
{
lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; uint8_t x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; 
lean_dec(x_815);
lean_dec(x_1);
x_832 = lean_ctor_get(x_822, 0);
lean_inc(x_832);
x_833 = lean_ctor_get(x_822, 1);
lean_inc(x_833);
if (lean_is_exclusive(x_822)) {
 lean_ctor_release(x_822, 0);
 lean_ctor_release(x_822, 1);
 x_834 = x_822;
} else {
 lean_dec_ref(x_822);
 x_834 = lean_box(0);
}
x_835 = lean_io_error_to_string(x_832);
x_836 = lean_box(3);
x_837 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_837, 0, x_835);
x_838 = lean_unbox(x_836);
lean_ctor_set_uint8(x_837, sizeof(void*)*1, x_838);
x_839 = lean_array_get_size(x_817);
x_840 = lean_array_push(x_817, x_837);
if (lean_is_scalar(x_820)) {
 x_841 = lean_alloc_ctor(0, 2, 1);
} else {
 x_841 = x_820;
}
lean_ctor_set(x_841, 0, x_840);
lean_ctor_set(x_841, 1, x_819);
lean_ctor_set_uint8(x_841, sizeof(void*)*2, x_818);
if (lean_is_scalar(x_816)) {
 x_842 = lean_alloc_ctor(1, 2, 0);
} else {
 x_842 = x_816;
 lean_ctor_set_tag(x_842, 1);
}
lean_ctor_set(x_842, 0, x_839);
lean_ctor_set(x_842, 1, x_841);
if (lean_is_scalar(x_834)) {
 x_843 = lean_alloc_ctor(0, 2, 0);
} else {
 x_843 = x_834;
 lean_ctor_set_tag(x_843, 0);
}
lean_ctor_set(x_843, 0, x_842);
lean_ctor_set(x_843, 1, x_833);
return x_843;
}
}
else
{
lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; 
lean_dec(x_1);
x_844 = lean_ctor_get(x_811, 1);
lean_inc(x_844);
if (lean_is_exclusive(x_811)) {
 lean_ctor_release(x_811, 0);
 lean_ctor_release(x_811, 1);
 x_845 = x_811;
} else {
 lean_dec_ref(x_811);
 x_845 = lean_box(0);
}
x_846 = lean_ctor_get(x_812, 0);
lean_inc(x_846);
x_847 = lean_ctor_get(x_812, 1);
lean_inc(x_847);
if (lean_is_exclusive(x_812)) {
 lean_ctor_release(x_812, 0);
 lean_ctor_release(x_812, 1);
 x_848 = x_812;
} else {
 lean_dec_ref(x_812);
 x_848 = lean_box(0);
}
if (lean_is_scalar(x_848)) {
 x_849 = lean_alloc_ctor(1, 2, 0);
} else {
 x_849 = x_848;
}
lean_ctor_set(x_849, 0, x_846);
lean_ctor_set(x_849, 1, x_847);
if (lean_is_scalar(x_845)) {
 x_850 = lean_alloc_ctor(0, 2, 0);
} else {
 x_850 = x_845;
}
lean_ctor_set(x_850, 0, x_849);
lean_ctor_set(x_850, 1, x_844);
return x_850;
}
}
else
{
lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; 
lean_dec(x_800);
lean_dec(x_799);
lean_dec(x_798);
lean_dec(x_797);
lean_dec(x_790);
lean_dec(x_787);
lean_dec(x_2);
x_851 = lean_ctor_get(x_805, 1);
lean_inc(x_851);
lean_dec(x_805);
x_852 = lean_ctor_get(x_806, 1);
lean_inc(x_852);
lean_dec(x_806);
lean_inc(x_1);
x_853 = l_Lake_fetchFileHash___redArg(x_1, x_3, x_801, x_852, x_851);
lean_dec(x_801);
x_854 = lean_ctor_get(x_853, 0);
lean_inc(x_854);
if (lean_obj_tag(x_854) == 0)
{
lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; uint64_t x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; uint8_t x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; 
x_855 = lean_ctor_get(x_853, 1);
lean_inc(x_855);
lean_dec(x_853);
x_856 = lean_ctor_get(x_854, 0);
lean_inc(x_856);
x_857 = lean_ctor_get(x_854, 1);
lean_inc(x_857);
if (lean_is_exclusive(x_854)) {
 lean_ctor_release(x_854, 0);
 lean_ctor_release(x_854, 1);
 x_858 = x_854;
} else {
 lean_dec_ref(x_854);
 x_858 = lean_box(0);
}
x_859 = lean_unbox_uint64(x_856);
lean_dec(x_856);
lean_inc(x_1);
x_860 = l_Lake_computeArtifactTrace(x_1, x_1, x_859, x_855);
x_861 = lean_ctor_get(x_860, 0);
lean_inc(x_861);
x_862 = lean_ctor_get(x_860, 1);
lean_inc(x_862);
if (lean_is_exclusive(x_860)) {
 lean_ctor_release(x_860, 0);
 lean_ctor_release(x_860, 1);
 x_863 = x_860;
} else {
 lean_dec_ref(x_860);
 x_863 = lean_box(0);
}
x_864 = lean_ctor_get(x_857, 0);
lean_inc(x_864);
x_865 = lean_ctor_get_uint8(x_857, sizeof(void*)*2);
if (lean_is_exclusive(x_857)) {
 lean_ctor_release(x_857, 0);
 lean_ctor_release(x_857, 1);
 x_866 = x_857;
} else {
 lean_dec_ref(x_857);
 x_866 = lean_box(0);
}
if (lean_is_scalar(x_866)) {
 x_867 = lean_alloc_ctor(0, 2, 1);
} else {
 x_867 = x_866;
}
lean_ctor_set(x_867, 0, x_864);
lean_ctor_set(x_867, 1, x_861);
lean_ctor_set_uint8(x_867, sizeof(void*)*2, x_865);
if (lean_is_scalar(x_858)) {
 x_868 = lean_alloc_ctor(0, 2, 0);
} else {
 x_868 = x_858;
}
lean_ctor_set(x_868, 0, x_1);
lean_ctor_set(x_868, 1, x_867);
if (lean_is_scalar(x_863)) {
 x_869 = lean_alloc_ctor(0, 2, 0);
} else {
 x_869 = x_863;
}
lean_ctor_set(x_869, 0, x_868);
lean_ctor_set(x_869, 1, x_862);
return x_869;
}
else
{
lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; 
lean_dec(x_1);
x_870 = lean_ctor_get(x_853, 1);
lean_inc(x_870);
if (lean_is_exclusive(x_853)) {
 lean_ctor_release(x_853, 0);
 lean_ctor_release(x_853, 1);
 x_871 = x_853;
} else {
 lean_dec_ref(x_853);
 x_871 = lean_box(0);
}
x_872 = lean_ctor_get(x_854, 0);
lean_inc(x_872);
x_873 = lean_ctor_get(x_854, 1);
lean_inc(x_873);
if (lean_is_exclusive(x_854)) {
 lean_ctor_release(x_854, 0);
 lean_ctor_release(x_854, 1);
 x_874 = x_854;
} else {
 lean_dec_ref(x_854);
 x_874 = lean_box(0);
}
if (lean_is_scalar(x_874)) {
 x_875 = lean_alloc_ctor(1, 2, 0);
} else {
 x_875 = x_874;
}
lean_ctor_set(x_875, 0, x_872);
lean_ctor_set(x_875, 1, x_873);
if (lean_is_scalar(x_871)) {
 x_876 = lean_alloc_ctor(0, 2, 0);
} else {
 x_876 = x_871;
}
lean_ctor_set(x_876, 0, x_875);
lean_ctor_set(x_876, 1, x_870);
return x_876;
}
}
}
}
}
else
{
lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; uint8_t x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1141; 
x_1026 = lean_ctor_get(x_25, 1);
x_1027 = lean_ctor_get(x_27, 0);
x_1028 = lean_ctor_get(x_27, 1);
lean_inc(x_1028);
lean_inc(x_1027);
lean_dec(x_27);
lean_inc(x_1026);
lean_inc(x_1028);
x_1029 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_1029, 0, x_1028);
lean_closure_set(x_1029, 1, x_1026);
lean_inc(x_1026);
lean_inc(x_1028);
x_1030 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_1030, 0, x_1028);
lean_closure_set(x_1030, 1, x_1026);
lean_inc(x_1029);
lean_inc(x_1028);
x_1031 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_1031, 0, x_1028);
lean_closure_set(x_1031, 1, x_1029);
lean_inc(x_1028);
lean_inc(x_1027);
x_1032 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_1032, 0, x_1027);
lean_closure_set(x_1032, 1, x_1028);
lean_closure_set(x_1032, 2, x_1026);
x_1033 = l_Lake_EStateT_instFunctor___redArg(x_1027);
x_1034 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_1034, 0, x_1028);
x_1035 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1035, 0, x_1033);
lean_ctor_set(x_1035, 1, x_1034);
lean_ctor_set(x_1035, 2, x_1032);
lean_ctor_set(x_1035, 3, x_1031);
lean_ctor_set(x_1035, 4, x_1030);
lean_ctor_set(x_25, 1, x_1029);
lean_ctor_set(x_25, 0, x_1035);
x_1036 = l_ReaderT_instMonad___redArg(x_25);
x_1037 = l_ReaderT_instMonad___redArg(x_1036);
x_1038 = l_ReaderT_instMonad___redArg(x_1037);
lean_inc(x_1038);
x_1039 = l_ReaderT_instMonad___redArg(x_1038);
x_1040 = lean_ctor_get(x_1038, 0);
lean_inc(x_1040);
if (lean_is_exclusive(x_1038)) {
 lean_ctor_release(x_1038, 0);
 lean_ctor_release(x_1038, 1);
 x_1041 = x_1038;
} else {
 lean_dec_ref(x_1038);
 x_1041 = lean_box(0);
}
x_1042 = lean_ctor_get(x_1040, 0);
lean_inc(x_1042);
lean_dec(x_1040);
lean_inc(x_1042);
x_1043 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_1043, 0, x_1042);
x_1044 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_1044, 0, x_1042);
if (lean_is_scalar(x_1041)) {
 x_1045 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1045 = x_1041;
}
lean_ctor_set(x_1045, 0, x_1043);
lean_ctor_set(x_1045, 1, x_1044);
x_1046 = l_Lake_EquipT_instFunctor___redArg(x_1045);
x_1047 = l_Lake_EquipT_instMonad___redArg(x_1039);
x_1048 = lean_ctor_get(x_11, 0);
lean_inc(x_1048);
x_1049 = lean_ctor_get_uint8(x_11, sizeof(void*)*2);
x_1050 = lean_ctor_get(x_11, 1);
lean_inc(x_1050);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_1051 = x_11;
} else {
 lean_dec_ref(x_11);
 x_1051 = lean_box(0);
}
x_1052 = l_Lake_buildFileUnlessUpToDate_x27___closed__0;
lean_inc(x_1);
x_1053 = lean_string_append(x_1, x_1052);
lean_inc(x_1053);
x_1054 = l_Lake_readTraceFile(x_1053, x_1048, x_12);
x_1055 = lean_ctor_get(x_1054, 0);
lean_inc(x_1055);
x_1056 = lean_ctor_get(x_1054, 1);
lean_inc(x_1056);
lean_dec(x_1054);
x_1057 = lean_ctor_get(x_1055, 0);
lean_inc(x_1057);
x_1058 = lean_ctor_get(x_1055, 1);
lean_inc(x_1058);
if (lean_is_exclusive(x_1055)) {
 lean_ctor_release(x_1055, 0);
 lean_ctor_release(x_1055, 1);
 x_1059 = x_1055;
} else {
 lean_dec_ref(x_1055);
 x_1059 = lean_box(0);
}
lean_inc(x_1050);
if (lean_is_scalar(x_1051)) {
 x_1141 = lean_alloc_ctor(0, 2, 1);
} else {
 x_1141 = x_1051;
}
lean_ctor_set(x_1141, 0, x_1058);
lean_ctor_set(x_1141, 1, x_1050);
lean_ctor_set_uint8(x_1141, sizeof(void*)*2, x_1049);
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_1059);
lean_dec(x_1047);
lean_dec(x_1046);
lean_dec(x_4);
x_1060 = x_6;
x_1061 = x_7;
x_1062 = x_8;
x_1063 = x_9;
x_1064 = x_10;
x_1065 = x_1141;
x_1066 = x_1056;
goto block_1140;
}
else
{
lean_object* x_1142; lean_object* x_1143; 
x_1142 = lean_ctor_get(x_7, 0);
lean_inc(x_1142);
x_1143 = lean_ctor_get(x_1142, 19);
lean_inc(x_1143);
lean_dec(x_1142);
if (lean_obj_tag(x_1143) == 0)
{
lean_dec(x_1059);
lean_dec(x_1047);
lean_dec(x_1046);
lean_dec(x_4);
x_1060 = x_6;
x_1061 = x_7;
x_1062 = x_8;
x_1063 = x_9;
x_1064 = x_10;
x_1065 = x_1141;
x_1066 = x_1056;
goto block_1140;
}
else
{
lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; uint64_t x_1192; lean_object* x_1193; lean_object* x_1194; 
x_1144 = lean_ctor_get(x_1143, 0);
lean_inc(x_1144);
lean_dec(x_1143);
x_1145 = lean_ctor_get(x_1050, 2);
lean_inc(x_1145);
x_1146 = lean_ctor_get(x_1050, 3);
lean_inc(x_1146);
x_1187 = l_Lake_instMonadWorkspaceJobM;
x_1188 = l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___redArg(x_1187, x_1046);
x_1189 = l_Lake_buildArtifactUnlessUpToDate___closed__11;
x_1190 = l_Lake_buildArtifactUnlessUpToDate___closed__12;
lean_inc(x_4);
x_1191 = l_Lake_instResolveArtifactsFileOutputHashArtifactOfMonadLakeEnvOfMonadLiftTBaseIOOfMonad___redArg(x_4, x_1188, x_1189, x_1047);
x_1192 = lean_unbox_uint64(x_1145);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1057);
lean_inc(x_6);
x_1193 = l_Lake_resolveArtifactsUsing_x3f___at___Lake_buildArtifactUnlessUpToDate_spec__0(x_1190, x_1191, x_6, x_1192, x_1057, x_1144, x_7, x_8, x_9, x_10, x_1141, x_1056);
x_1194 = lean_ctor_get(x_1193, 0);
lean_inc(x_1194);
if (lean_obj_tag(x_1194) == 0)
{
lean_object* x_1195; 
x_1195 = lean_ctor_get(x_1194, 0);
lean_inc(x_1195);
if (lean_obj_tag(x_1195) == 0)
{
lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; uint8_t x_1201; 
x_1196 = lean_ctor_get(x_1193, 1);
lean_inc(x_1196);
lean_dec(x_1193);
x_1197 = lean_ctor_get(x_1194, 1);
lean_inc(x_1197);
lean_dec(x_1194);
x_1198 = l_Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0(x_6, x_1, x_1050, x_1057, x_1146, x_7, x_8, x_9, x_10, x_1197, x_1196);
lean_dec(x_1146);
x_1199 = lean_ctor_get(x_1198, 0);
lean_inc(x_1199);
x_1200 = lean_ctor_get(x_1199, 0);
lean_inc(x_1200);
x_1201 = lean_unbox(x_1200);
lean_dec(x_1200);
if (x_1201 == 0)
{
lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; 
x_1202 = lean_ctor_get(x_1198, 1);
lean_inc(x_1202);
lean_dec(x_1198);
x_1203 = lean_ctor_get(x_1199, 1);
lean_inc(x_1203);
lean_dec(x_1199);
lean_inc(x_10);
lean_inc(x_1);
x_1204 = l_Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_3, x_1050, x_1053, x_6, x_7, x_8, x_9, x_10, x_1203, x_1202);
lean_dec(x_1053);
x_1205 = lean_ctor_get(x_1204, 0);
lean_inc(x_1205);
if (lean_obj_tag(x_1205) == 0)
{
lean_object* x_1206; lean_object* x_1207; 
x_1206 = lean_ctor_get(x_1204, 1);
lean_inc(x_1206);
lean_dec(x_1204);
x_1207 = lean_ctor_get(x_1205, 1);
lean_inc(x_1207);
lean_dec(x_1205);
x_1147 = x_10;
x_1148 = x_1207;
x_1149 = x_1206;
goto block_1186;
}
else
{
lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; 
lean_dec(x_1145);
lean_dec(x_1144);
lean_dec(x_1059);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_1);
x_1208 = lean_ctor_get(x_1204, 1);
lean_inc(x_1208);
if (lean_is_exclusive(x_1204)) {
 lean_ctor_release(x_1204, 0);
 lean_ctor_release(x_1204, 1);
 x_1209 = x_1204;
} else {
 lean_dec_ref(x_1204);
 x_1209 = lean_box(0);
}
x_1210 = lean_ctor_get(x_1205, 0);
lean_inc(x_1210);
x_1211 = lean_ctor_get(x_1205, 1);
lean_inc(x_1211);
if (lean_is_exclusive(x_1205)) {
 lean_ctor_release(x_1205, 0);
 lean_ctor_release(x_1205, 1);
 x_1212 = x_1205;
} else {
 lean_dec_ref(x_1205);
 x_1212 = lean_box(0);
}
if (lean_is_scalar(x_1212)) {
 x_1213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1213 = x_1212;
}
lean_ctor_set(x_1213, 0, x_1210);
lean_ctor_set(x_1213, 1, x_1211);
if (lean_is_scalar(x_1209)) {
 x_1214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1214 = x_1209;
}
lean_ctor_set(x_1214, 0, x_1213);
lean_ctor_set(x_1214, 1, x_1208);
return x_1214;
}
}
else
{
lean_object* x_1215; lean_object* x_1216; 
lean_dec(x_1053);
lean_dec(x_1050);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_1215 = lean_ctor_get(x_1198, 1);
lean_inc(x_1215);
lean_dec(x_1198);
x_1216 = lean_ctor_get(x_1199, 1);
lean_inc(x_1216);
lean_dec(x_1199);
x_1147 = x_10;
x_1148 = x_1216;
x_1149 = x_1215;
goto block_1186;
}
}
else
{
lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1234; 
lean_dec(x_1146);
lean_dec(x_1145);
lean_dec(x_1144);
lean_dec(x_1059);
lean_dec(x_1053);
lean_dec(x_1050);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1217 = lean_ctor_get(x_1193, 1);
lean_inc(x_1217);
lean_dec(x_1193);
x_1218 = lean_ctor_get(x_1194, 1);
lean_inc(x_1218);
if (lean_is_exclusive(x_1194)) {
 lean_ctor_release(x_1194, 0);
 lean_ctor_release(x_1194, 1);
 x_1219 = x_1194;
} else {
 lean_dec_ref(x_1194);
 x_1219 = lean_box(0);
}
x_1220 = lean_ctor_get(x_1195, 0);
lean_inc(x_1220);
lean_dec(x_1195);
x_1234 = l_System_FilePath_pathExists(x_1, x_1217);
if (x_5 == 0)
{
lean_object* x_1235; 
lean_dec(x_1219);
x_1235 = lean_ctor_get(x_1234, 1);
lean_inc(x_1235);
lean_dec(x_1234);
x_1221 = x_1218;
x_1222 = x_1235;
goto block_1233;
}
else
{
lean_object* x_1236; uint8_t x_1237; 
x_1236 = lean_ctor_get(x_1234, 0);
lean_inc(x_1236);
x_1237 = lean_unbox(x_1236);
lean_dec(x_1236);
if (x_1237 == 0)
{
lean_object* x_1238; lean_object* x_1239; uint8_t x_1240; lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; uint8_t x_1249; lean_object* x_1250; lean_object* x_1251; 
x_1238 = lean_ctor_get(x_1234, 1);
lean_inc(x_1238);
lean_dec(x_1234);
x_1239 = lean_ctor_get(x_1218, 0);
lean_inc(x_1239);
x_1240 = lean_ctor_get_uint8(x_1218, sizeof(void*)*2);
x_1241 = lean_ctor_get(x_1218, 1);
lean_inc(x_1241);
if (lean_is_exclusive(x_1218)) {
 lean_ctor_release(x_1218, 0);
 lean_ctor_release(x_1218, 1);
 x_1242 = x_1218;
} else {
 lean_dec_ref(x_1218);
 x_1242 = lean_box(0);
}
x_1243 = lean_ctor_get(x_1220, 0);
lean_inc(x_1243);
x_1244 = lean_ctor_get(x_1220, 3);
lean_inc(x_1244);
x_1245 = l_Lake_buildArtifactUnlessUpToDate___closed__13;
x_1246 = lean_string_append(x_1245, x_1);
x_1247 = lean_box(0);
x_1248 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1248, 0, x_1246);
x_1249 = lean_unbox(x_1247);
lean_ctor_set_uint8(x_1248, sizeof(void*)*1, x_1249);
x_1250 = lean_array_push(x_1239, x_1248);
x_1251 = l_Lake_copyFile(x_1243, x_1, x_1238);
lean_dec(x_1243);
if (lean_obj_tag(x_1251) == 0)
{
lean_object* x_1252; uint64_t x_1253; lean_object* x_1254; 
x_1252 = lean_ctor_get(x_1251, 1);
lean_inc(x_1252);
lean_dec(x_1251);
x_1253 = lean_unbox_uint64(x_1244);
lean_dec(x_1244);
lean_inc(x_1);
x_1254 = l_Lake_writeFileHash(x_1, x_1253, x_1252);
if (lean_obj_tag(x_1254) == 0)
{
lean_object* x_1255; lean_object* x_1256; 
lean_dec(x_1219);
x_1255 = lean_ctor_get(x_1254, 1);
lean_inc(x_1255);
lean_dec(x_1254);
if (lean_is_scalar(x_1242)) {
 x_1256 = lean_alloc_ctor(0, 2, 1);
} else {
 x_1256 = x_1242;
}
lean_ctor_set(x_1256, 0, x_1250);
lean_ctor_set(x_1256, 1, x_1241);
lean_ctor_set_uint8(x_1256, sizeof(void*)*2, x_1240);
x_1221 = x_1256;
x_1222 = x_1255;
goto block_1233;
}
else
{
lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; uint8_t x_1263; lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; 
lean_dec(x_1220);
lean_dec(x_1057);
lean_dec(x_1);
x_1257 = lean_ctor_get(x_1254, 0);
lean_inc(x_1257);
x_1258 = lean_ctor_get(x_1254, 1);
lean_inc(x_1258);
if (lean_is_exclusive(x_1254)) {
 lean_ctor_release(x_1254, 0);
 lean_ctor_release(x_1254, 1);
 x_1259 = x_1254;
} else {
 lean_dec_ref(x_1254);
 x_1259 = lean_box(0);
}
x_1260 = lean_io_error_to_string(x_1257);
x_1261 = lean_box(3);
x_1262 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1262, 0, x_1260);
x_1263 = lean_unbox(x_1261);
lean_ctor_set_uint8(x_1262, sizeof(void*)*1, x_1263);
x_1264 = lean_array_get_size(x_1250);
x_1265 = lean_array_push(x_1250, x_1262);
if (lean_is_scalar(x_1242)) {
 x_1266 = lean_alloc_ctor(0, 2, 1);
} else {
 x_1266 = x_1242;
}
lean_ctor_set(x_1266, 0, x_1265);
lean_ctor_set(x_1266, 1, x_1241);
lean_ctor_set_uint8(x_1266, sizeof(void*)*2, x_1240);
if (lean_is_scalar(x_1219)) {
 x_1267 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1267 = x_1219;
 lean_ctor_set_tag(x_1267, 1);
}
lean_ctor_set(x_1267, 0, x_1264);
lean_ctor_set(x_1267, 1, x_1266);
if (lean_is_scalar(x_1259)) {
 x_1268 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1268 = x_1259;
 lean_ctor_set_tag(x_1268, 0);
}
lean_ctor_set(x_1268, 0, x_1267);
lean_ctor_set(x_1268, 1, x_1258);
return x_1268;
}
}
else
{
lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; uint8_t x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; 
lean_dec(x_1244);
lean_dec(x_1220);
lean_dec(x_1057);
lean_dec(x_1);
x_1269 = lean_ctor_get(x_1251, 0);
lean_inc(x_1269);
x_1270 = lean_ctor_get(x_1251, 1);
lean_inc(x_1270);
if (lean_is_exclusive(x_1251)) {
 lean_ctor_release(x_1251, 0);
 lean_ctor_release(x_1251, 1);
 x_1271 = x_1251;
} else {
 lean_dec_ref(x_1251);
 x_1271 = lean_box(0);
}
x_1272 = lean_io_error_to_string(x_1269);
x_1273 = lean_box(3);
x_1274 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1274, 0, x_1272);
x_1275 = lean_unbox(x_1273);
lean_ctor_set_uint8(x_1274, sizeof(void*)*1, x_1275);
x_1276 = lean_array_get_size(x_1250);
x_1277 = lean_array_push(x_1250, x_1274);
if (lean_is_scalar(x_1242)) {
 x_1278 = lean_alloc_ctor(0, 2, 1);
} else {
 x_1278 = x_1242;
}
lean_ctor_set(x_1278, 0, x_1277);
lean_ctor_set(x_1278, 1, x_1241);
lean_ctor_set_uint8(x_1278, sizeof(void*)*2, x_1240);
if (lean_is_scalar(x_1219)) {
 x_1279 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1279 = x_1219;
 lean_ctor_set_tag(x_1279, 1);
}
lean_ctor_set(x_1279, 0, x_1276);
lean_ctor_set(x_1279, 1, x_1278);
if (lean_is_scalar(x_1271)) {
 x_1280 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1280 = x_1271;
 lean_ctor_set_tag(x_1280, 0);
}
lean_ctor_set(x_1280, 0, x_1279);
lean_ctor_set(x_1280, 1, x_1270);
return x_1280;
}
}
else
{
lean_object* x_1281; 
lean_dec(x_1219);
x_1281 = lean_ctor_get(x_1234, 1);
lean_inc(x_1281);
lean_dec(x_1234);
x_1221 = x_1218;
x_1222 = x_1281;
goto block_1233;
}
}
block_1233:
{
lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; uint8_t x_1228; lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; 
x_1223 = l_Lake_SavedTrace_replayIfExists___redArg(x_1057, x_1221, x_1222);
lean_dec(x_1057);
x_1224 = lean_ctor_get(x_1223, 0);
lean_inc(x_1224);
x_1225 = lean_ctor_get(x_1224, 1);
lean_inc(x_1225);
lean_dec(x_1224);
x_1226 = lean_ctor_get(x_1223, 1);
lean_inc(x_1226);
lean_dec(x_1223);
x_1227 = lean_ctor_get(x_1225, 0);
lean_inc(x_1227);
x_1228 = lean_ctor_get_uint8(x_1225, sizeof(void*)*2);
if (lean_is_exclusive(x_1225)) {
 lean_ctor_release(x_1225, 0);
 lean_ctor_release(x_1225, 1);
 x_1229 = x_1225;
} else {
 lean_dec_ref(x_1225);
 x_1229 = lean_box(0);
}
lean_inc(x_1220);
x_1230 = l_Lake_Artifact_trace(x_1220);
if (lean_is_scalar(x_1229)) {
 x_1231 = lean_alloc_ctor(0, 2, 1);
} else {
 x_1231 = x_1229;
}
lean_ctor_set(x_1231, 0, x_1227);
lean_ctor_set(x_1231, 1, x_1230);
lean_ctor_set_uint8(x_1231, sizeof(void*)*2, x_1228);
if (x_5 == 0)
{
lean_object* x_1232; 
lean_dec(x_1);
x_1232 = lean_ctor_get(x_1220, 0);
lean_inc(x_1232);
lean_dec(x_1220);
x_13 = x_1226;
x_14 = x_1231;
x_15 = x_1232;
goto block_18;
}
else
{
lean_dec(x_1220);
x_13 = x_1226;
x_14 = x_1231;
x_15 = x_1;
goto block_18;
}
}
}
}
else
{
lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; 
lean_dec(x_1146);
lean_dec(x_1145);
lean_dec(x_1144);
lean_dec(x_1059);
lean_dec(x_1057);
lean_dec(x_1053);
lean_dec(x_1050);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1282 = lean_ctor_get(x_1193, 1);
lean_inc(x_1282);
if (lean_is_exclusive(x_1193)) {
 lean_ctor_release(x_1193, 0);
 lean_ctor_release(x_1193, 1);
 x_1283 = x_1193;
} else {
 lean_dec_ref(x_1193);
 x_1283 = lean_box(0);
}
x_1284 = lean_ctor_get(x_1194, 0);
lean_inc(x_1284);
x_1285 = lean_ctor_get(x_1194, 1);
lean_inc(x_1285);
if (lean_is_exclusive(x_1194)) {
 lean_ctor_release(x_1194, 0);
 lean_ctor_release(x_1194, 1);
 x_1286 = x_1194;
} else {
 lean_dec_ref(x_1194);
 x_1286 = lean_box(0);
}
if (lean_is_scalar(x_1286)) {
 x_1287 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1287 = x_1286;
}
lean_ctor_set(x_1287, 0, x_1284);
lean_ctor_set(x_1287, 1, x_1285);
if (lean_is_scalar(x_1283)) {
 x_1288 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1288 = x_1283;
}
lean_ctor_set(x_1288, 0, x_1287);
lean_ctor_set(x_1288, 1, x_1282);
return x_1288;
}
block_1186:
{
lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; uint8_t x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; 
x_1150 = lean_ctor_get(x_1147, 1);
lean_inc(x_1150);
lean_dec(x_1147);
x_1151 = lean_ctor_get(x_1150, 1);
lean_inc(x_1151);
lean_dec(x_1150);
x_1152 = lean_ctor_get(x_1148, 0);
lean_inc(x_1152);
x_1153 = lean_ctor_get_uint8(x_1148, sizeof(void*)*2);
x_1154 = lean_ctor_get(x_1148, 1);
lean_inc(x_1154);
if (lean_is_exclusive(x_1148)) {
 lean_ctor_release(x_1148, 0);
 lean_ctor_release(x_1148, 1);
 x_1155 = x_1148;
} else {
 lean_dec_ref(x_1148);
 x_1155 = lean_box(0);
}
x_1156 = lean_ctor_get(x_1151, 6);
lean_inc(x_1156);
lean_dec(x_1151);
lean_inc(x_1);
x_1157 = l_Lake_Cache_saveArtifact(x_1156, x_1, x_4, x_3, x_1149);
lean_dec(x_4);
if (lean_obj_tag(x_1157) == 0)
{
lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; uint64_t x_1165; lean_object* x_1166; lean_object* x_1167; uint64_t x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; 
lean_dec(x_1154);
lean_dec(x_1059);
x_1158 = lean_ctor_get(x_1157, 0);
lean_inc(x_1158);
x_1159 = lean_ctor_get(x_1157, 1);
lean_inc(x_1159);
lean_dec(x_1157);
x_1160 = lean_st_ref_take(x_1144, x_1159);
x_1161 = lean_ctor_get(x_1160, 0);
lean_inc(x_1161);
x_1162 = lean_ctor_get(x_1160, 1);
lean_inc(x_1162);
lean_dec(x_1160);
x_1163 = lean_ctor_get(x_1158, 0);
lean_inc(x_1163);
x_1164 = lean_ctor_get(x_1158, 3);
lean_inc(x_1164);
x_1165 = lean_unbox_uint64(x_1164);
lean_dec(x_1164);
x_1166 = lean_uint64_to_nat(x_1165);
x_1167 = l_Lean_bignumToJson(x_1166);
x_1168 = lean_unbox_uint64(x_1145);
lean_dec(x_1145);
x_1169 = l_Lake_CacheMap_insertCore(x_1168, x_1167, x_1161);
x_1170 = lean_st_ref_set(x_1144, x_1169, x_1162);
lean_dec(x_1144);
x_1171 = lean_ctor_get(x_1170, 1);
lean_inc(x_1171);
lean_dec(x_1170);
x_1172 = l_Lake_Artifact_trace(x_1158);
if (lean_is_scalar(x_1155)) {
 x_1173 = lean_alloc_ctor(0, 2, 1);
} else {
 x_1173 = x_1155;
}
lean_ctor_set(x_1173, 0, x_1152);
lean_ctor_set(x_1173, 1, x_1172);
lean_ctor_set_uint8(x_1173, sizeof(void*)*2, x_1153);
if (x_5 == 0)
{
lean_dec(x_1);
x_19 = x_1171;
x_20 = x_1173;
x_21 = x_1163;
goto block_24;
}
else
{
lean_dec(x_1163);
x_19 = x_1171;
x_20 = x_1173;
x_21 = x_1;
goto block_24;
}
}
else
{
lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; uint8_t x_1180; lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; 
lean_dec(x_1145);
lean_dec(x_1144);
lean_dec(x_1);
x_1174 = lean_ctor_get(x_1157, 0);
lean_inc(x_1174);
x_1175 = lean_ctor_get(x_1157, 1);
lean_inc(x_1175);
if (lean_is_exclusive(x_1157)) {
 lean_ctor_release(x_1157, 0);
 lean_ctor_release(x_1157, 1);
 x_1176 = x_1157;
} else {
 lean_dec_ref(x_1157);
 x_1176 = lean_box(0);
}
x_1177 = lean_io_error_to_string(x_1174);
x_1178 = lean_box(3);
x_1179 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1179, 0, x_1177);
x_1180 = lean_unbox(x_1178);
lean_ctor_set_uint8(x_1179, sizeof(void*)*1, x_1180);
x_1181 = lean_array_get_size(x_1152);
x_1182 = lean_array_push(x_1152, x_1179);
if (lean_is_scalar(x_1155)) {
 x_1183 = lean_alloc_ctor(0, 2, 1);
} else {
 x_1183 = x_1155;
}
lean_ctor_set(x_1183, 0, x_1182);
lean_ctor_set(x_1183, 1, x_1154);
lean_ctor_set_uint8(x_1183, sizeof(void*)*2, x_1153);
if (lean_is_scalar(x_1059)) {
 x_1184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1184 = x_1059;
 lean_ctor_set_tag(x_1184, 1);
}
lean_ctor_set(x_1184, 0, x_1181);
lean_ctor_set(x_1184, 1, x_1183);
if (lean_is_scalar(x_1176)) {
 x_1185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1185 = x_1176;
 lean_ctor_set_tag(x_1185, 0);
}
lean_ctor_set(x_1185, 0, x_1184);
lean_ctor_set(x_1185, 1, x_1175);
return x_1185;
}
}
}
}
block_1140:
{
lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; uint8_t x_1071; 
x_1067 = lean_ctor_get(x_1050, 3);
lean_inc(x_1067);
x_1068 = l_Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0(x_1060, x_1, x_1050, x_1057, x_1067, x_1061, x_1062, x_1063, x_1064, x_1065, x_1066);
lean_dec(x_1067);
x_1069 = lean_ctor_get(x_1068, 0);
lean_inc(x_1069);
x_1070 = lean_ctor_get(x_1069, 0);
lean_inc(x_1070);
x_1071 = lean_unbox(x_1070);
lean_dec(x_1070);
if (x_1071 == 0)
{
lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; 
x_1072 = lean_ctor_get(x_1068, 1);
lean_inc(x_1072);
lean_dec(x_1068);
x_1073 = lean_ctor_get(x_1069, 1);
lean_inc(x_1073);
lean_dec(x_1069);
lean_inc(x_1);
x_1074 = l_Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_3, x_1050, x_1053, x_1060, x_1061, x_1062, x_1063, x_1064, x_1073, x_1072);
lean_dec(x_1053);
x_1075 = lean_ctor_get(x_1074, 0);
lean_inc(x_1075);
if (lean_obj_tag(x_1075) == 0)
{
lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; uint8_t x_1081; lean_object* x_1082; lean_object* x_1083; uint64_t x_1084; lean_object* x_1085; 
x_1076 = lean_ctor_get(x_1075, 1);
lean_inc(x_1076);
x_1077 = lean_ctor_get(x_1074, 1);
lean_inc(x_1077);
lean_dec(x_1074);
x_1078 = lean_ctor_get(x_1075, 0);
lean_inc(x_1078);
if (lean_is_exclusive(x_1075)) {
 lean_ctor_release(x_1075, 0);
 lean_ctor_release(x_1075, 1);
 x_1079 = x_1075;
} else {
 lean_dec_ref(x_1075);
 x_1079 = lean_box(0);
}
x_1080 = lean_ctor_get(x_1076, 0);
lean_inc(x_1080);
x_1081 = lean_ctor_get_uint8(x_1076, sizeof(void*)*2);
x_1082 = lean_ctor_get(x_1076, 1);
lean_inc(x_1082);
if (lean_is_exclusive(x_1076)) {
 lean_ctor_release(x_1076, 0);
 lean_ctor_release(x_1076, 1);
 x_1083 = x_1076;
} else {
 lean_dec_ref(x_1076);
 x_1083 = lean_box(0);
}
x_1084 = lean_unbox_uint64(x_1078);
lean_inc(x_1);
x_1085 = l_Lake_writeFileHash(x_1, x_1084, x_1077);
if (lean_obj_tag(x_1085) == 0)
{
lean_object* x_1086; uint64_t x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; 
lean_dec(x_1082);
x_1086 = lean_ctor_get(x_1085, 1);
lean_inc(x_1086);
lean_dec(x_1085);
x_1087 = lean_unbox_uint64(x_1078);
lean_dec(x_1078);
lean_inc(x_1);
x_1088 = l_Lake_computeArtifactTrace(x_1, x_1, x_1087, x_1086);
x_1089 = lean_ctor_get(x_1088, 0);
lean_inc(x_1089);
x_1090 = lean_ctor_get(x_1088, 1);
lean_inc(x_1090);
if (lean_is_exclusive(x_1088)) {
 lean_ctor_release(x_1088, 0);
 lean_ctor_release(x_1088, 1);
 x_1091 = x_1088;
} else {
 lean_dec_ref(x_1088);
 x_1091 = lean_box(0);
}
if (lean_is_scalar(x_1083)) {
 x_1092 = lean_alloc_ctor(0, 2, 1);
} else {
 x_1092 = x_1083;
}
lean_ctor_set(x_1092, 0, x_1080);
lean_ctor_set(x_1092, 1, x_1089);
lean_ctor_set_uint8(x_1092, sizeof(void*)*2, x_1081);
if (lean_is_scalar(x_1079)) {
 x_1093 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1093 = x_1079;
}
lean_ctor_set(x_1093, 0, x_1);
lean_ctor_set(x_1093, 1, x_1092);
if (lean_is_scalar(x_1091)) {
 x_1094 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1094 = x_1091;
}
lean_ctor_set(x_1094, 0, x_1093);
lean_ctor_set(x_1094, 1, x_1090);
return x_1094;
}
else
{
lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; uint8_t x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; 
lean_dec(x_1078);
lean_dec(x_1);
x_1095 = lean_ctor_get(x_1085, 0);
lean_inc(x_1095);
x_1096 = lean_ctor_get(x_1085, 1);
lean_inc(x_1096);
if (lean_is_exclusive(x_1085)) {
 lean_ctor_release(x_1085, 0);
 lean_ctor_release(x_1085, 1);
 x_1097 = x_1085;
} else {
 lean_dec_ref(x_1085);
 x_1097 = lean_box(0);
}
x_1098 = lean_io_error_to_string(x_1095);
x_1099 = lean_box(3);
x_1100 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1100, 0, x_1098);
x_1101 = lean_unbox(x_1099);
lean_ctor_set_uint8(x_1100, sizeof(void*)*1, x_1101);
x_1102 = lean_array_get_size(x_1080);
x_1103 = lean_array_push(x_1080, x_1100);
if (lean_is_scalar(x_1083)) {
 x_1104 = lean_alloc_ctor(0, 2, 1);
} else {
 x_1104 = x_1083;
}
lean_ctor_set(x_1104, 0, x_1103);
lean_ctor_set(x_1104, 1, x_1082);
lean_ctor_set_uint8(x_1104, sizeof(void*)*2, x_1081);
if (lean_is_scalar(x_1079)) {
 x_1105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1105 = x_1079;
 lean_ctor_set_tag(x_1105, 1);
}
lean_ctor_set(x_1105, 0, x_1102);
lean_ctor_set(x_1105, 1, x_1104);
if (lean_is_scalar(x_1097)) {
 x_1106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1106 = x_1097;
 lean_ctor_set_tag(x_1106, 0);
}
lean_ctor_set(x_1106, 0, x_1105);
lean_ctor_set(x_1106, 1, x_1096);
return x_1106;
}
}
else
{
lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; 
lean_dec(x_1);
x_1107 = lean_ctor_get(x_1074, 1);
lean_inc(x_1107);
if (lean_is_exclusive(x_1074)) {
 lean_ctor_release(x_1074, 0);
 lean_ctor_release(x_1074, 1);
 x_1108 = x_1074;
} else {
 lean_dec_ref(x_1074);
 x_1108 = lean_box(0);
}
x_1109 = lean_ctor_get(x_1075, 0);
lean_inc(x_1109);
x_1110 = lean_ctor_get(x_1075, 1);
lean_inc(x_1110);
if (lean_is_exclusive(x_1075)) {
 lean_ctor_release(x_1075, 0);
 lean_ctor_release(x_1075, 1);
 x_1111 = x_1075;
} else {
 lean_dec_ref(x_1075);
 x_1111 = lean_box(0);
}
if (lean_is_scalar(x_1111)) {
 x_1112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1112 = x_1111;
}
lean_ctor_set(x_1112, 0, x_1109);
lean_ctor_set(x_1112, 1, x_1110);
if (lean_is_scalar(x_1108)) {
 x_1113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1113 = x_1108;
}
lean_ctor_set(x_1113, 0, x_1112);
lean_ctor_set(x_1113, 1, x_1107);
return x_1113;
}
}
else
{
lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; 
lean_dec(x_1063);
lean_dec(x_1062);
lean_dec(x_1061);
lean_dec(x_1060);
lean_dec(x_1053);
lean_dec(x_1050);
lean_dec(x_2);
x_1114 = lean_ctor_get(x_1068, 1);
lean_inc(x_1114);
lean_dec(x_1068);
x_1115 = lean_ctor_get(x_1069, 1);
lean_inc(x_1115);
lean_dec(x_1069);
lean_inc(x_1);
x_1116 = l_Lake_fetchFileHash___redArg(x_1, x_3, x_1064, x_1115, x_1114);
lean_dec(x_1064);
x_1117 = lean_ctor_get(x_1116, 0);
lean_inc(x_1117);
if (lean_obj_tag(x_1117) == 0)
{
lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; uint64_t x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; uint8_t x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; 
x_1118 = lean_ctor_get(x_1116, 1);
lean_inc(x_1118);
lean_dec(x_1116);
x_1119 = lean_ctor_get(x_1117, 0);
lean_inc(x_1119);
x_1120 = lean_ctor_get(x_1117, 1);
lean_inc(x_1120);
if (lean_is_exclusive(x_1117)) {
 lean_ctor_release(x_1117, 0);
 lean_ctor_release(x_1117, 1);
 x_1121 = x_1117;
} else {
 lean_dec_ref(x_1117);
 x_1121 = lean_box(0);
}
x_1122 = lean_unbox_uint64(x_1119);
lean_dec(x_1119);
lean_inc(x_1);
x_1123 = l_Lake_computeArtifactTrace(x_1, x_1, x_1122, x_1118);
x_1124 = lean_ctor_get(x_1123, 0);
lean_inc(x_1124);
x_1125 = lean_ctor_get(x_1123, 1);
lean_inc(x_1125);
if (lean_is_exclusive(x_1123)) {
 lean_ctor_release(x_1123, 0);
 lean_ctor_release(x_1123, 1);
 x_1126 = x_1123;
} else {
 lean_dec_ref(x_1123);
 x_1126 = lean_box(0);
}
x_1127 = lean_ctor_get(x_1120, 0);
lean_inc(x_1127);
x_1128 = lean_ctor_get_uint8(x_1120, sizeof(void*)*2);
if (lean_is_exclusive(x_1120)) {
 lean_ctor_release(x_1120, 0);
 lean_ctor_release(x_1120, 1);
 x_1129 = x_1120;
} else {
 lean_dec_ref(x_1120);
 x_1129 = lean_box(0);
}
if (lean_is_scalar(x_1129)) {
 x_1130 = lean_alloc_ctor(0, 2, 1);
} else {
 x_1130 = x_1129;
}
lean_ctor_set(x_1130, 0, x_1127);
lean_ctor_set(x_1130, 1, x_1124);
lean_ctor_set_uint8(x_1130, sizeof(void*)*2, x_1128);
if (lean_is_scalar(x_1121)) {
 x_1131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1131 = x_1121;
}
lean_ctor_set(x_1131, 0, x_1);
lean_ctor_set(x_1131, 1, x_1130);
if (lean_is_scalar(x_1126)) {
 x_1132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1132 = x_1126;
}
lean_ctor_set(x_1132, 0, x_1131);
lean_ctor_set(x_1132, 1, x_1125);
return x_1132;
}
else
{
lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; 
lean_dec(x_1);
x_1133 = lean_ctor_get(x_1116, 1);
lean_inc(x_1133);
if (lean_is_exclusive(x_1116)) {
 lean_ctor_release(x_1116, 0);
 lean_ctor_release(x_1116, 1);
 x_1134 = x_1116;
} else {
 lean_dec_ref(x_1116);
 x_1134 = lean_box(0);
}
x_1135 = lean_ctor_get(x_1117, 0);
lean_inc(x_1135);
x_1136 = lean_ctor_get(x_1117, 1);
lean_inc(x_1136);
if (lean_is_exclusive(x_1117)) {
 lean_ctor_release(x_1117, 0);
 lean_ctor_release(x_1117, 1);
 x_1137 = x_1117;
} else {
 lean_dec_ref(x_1117);
 x_1137 = lean_box(0);
}
if (lean_is_scalar(x_1137)) {
 x_1138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1138 = x_1137;
}
lean_ctor_set(x_1138, 0, x_1135);
lean_ctor_set(x_1138, 1, x_1136);
if (lean_is_scalar(x_1134)) {
 x_1139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1139 = x_1134;
}
lean_ctor_set(x_1139, 0, x_1138);
lean_ctor_set(x_1139, 1, x_1133);
return x_1139;
}
}
}
}
}
else
{
lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; uint8_t x_1315; lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1407; 
x_1289 = lean_ctor_get(x_25, 0);
x_1290 = lean_ctor_get(x_25, 1);
lean_inc(x_1290);
lean_inc(x_1289);
lean_dec(x_25);
x_1291 = lean_ctor_get(x_1289, 0);
lean_inc(x_1291);
x_1292 = lean_ctor_get(x_1289, 1);
lean_inc(x_1292);
if (lean_is_exclusive(x_1289)) {
 lean_ctor_release(x_1289, 0);
 lean_ctor_release(x_1289, 1);
 lean_ctor_release(x_1289, 2);
 lean_ctor_release(x_1289, 3);
 lean_ctor_release(x_1289, 4);
 x_1293 = x_1289;
} else {
 lean_dec_ref(x_1289);
 x_1293 = lean_box(0);
}
lean_inc(x_1290);
lean_inc(x_1292);
x_1294 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_1294, 0, x_1292);
lean_closure_set(x_1294, 1, x_1290);
lean_inc(x_1290);
lean_inc(x_1292);
x_1295 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_1295, 0, x_1292);
lean_closure_set(x_1295, 1, x_1290);
lean_inc(x_1294);
lean_inc(x_1292);
x_1296 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_1296, 0, x_1292);
lean_closure_set(x_1296, 1, x_1294);
lean_inc(x_1292);
lean_inc(x_1291);
x_1297 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_1297, 0, x_1291);
lean_closure_set(x_1297, 1, x_1292);
lean_closure_set(x_1297, 2, x_1290);
x_1298 = l_Lake_EStateT_instFunctor___redArg(x_1291);
x_1299 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_1299, 0, x_1292);
if (lean_is_scalar(x_1293)) {
 x_1300 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1300 = x_1293;
}
lean_ctor_set(x_1300, 0, x_1298);
lean_ctor_set(x_1300, 1, x_1299);
lean_ctor_set(x_1300, 2, x_1297);
lean_ctor_set(x_1300, 3, x_1296);
lean_ctor_set(x_1300, 4, x_1295);
x_1301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1301, 0, x_1300);
lean_ctor_set(x_1301, 1, x_1294);
x_1302 = l_ReaderT_instMonad___redArg(x_1301);
x_1303 = l_ReaderT_instMonad___redArg(x_1302);
x_1304 = l_ReaderT_instMonad___redArg(x_1303);
lean_inc(x_1304);
x_1305 = l_ReaderT_instMonad___redArg(x_1304);
x_1306 = lean_ctor_get(x_1304, 0);
lean_inc(x_1306);
if (lean_is_exclusive(x_1304)) {
 lean_ctor_release(x_1304, 0);
 lean_ctor_release(x_1304, 1);
 x_1307 = x_1304;
} else {
 lean_dec_ref(x_1304);
 x_1307 = lean_box(0);
}
x_1308 = lean_ctor_get(x_1306, 0);
lean_inc(x_1308);
lean_dec(x_1306);
lean_inc(x_1308);
x_1309 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_1309, 0, x_1308);
x_1310 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_1310, 0, x_1308);
if (lean_is_scalar(x_1307)) {
 x_1311 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1311 = x_1307;
}
lean_ctor_set(x_1311, 0, x_1309);
lean_ctor_set(x_1311, 1, x_1310);
x_1312 = l_Lake_EquipT_instFunctor___redArg(x_1311);
x_1313 = l_Lake_EquipT_instMonad___redArg(x_1305);
x_1314 = lean_ctor_get(x_11, 0);
lean_inc(x_1314);
x_1315 = lean_ctor_get_uint8(x_11, sizeof(void*)*2);
x_1316 = lean_ctor_get(x_11, 1);
lean_inc(x_1316);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_1317 = x_11;
} else {
 lean_dec_ref(x_11);
 x_1317 = lean_box(0);
}
x_1318 = l_Lake_buildFileUnlessUpToDate_x27___closed__0;
lean_inc(x_1);
x_1319 = lean_string_append(x_1, x_1318);
lean_inc(x_1319);
x_1320 = l_Lake_readTraceFile(x_1319, x_1314, x_12);
x_1321 = lean_ctor_get(x_1320, 0);
lean_inc(x_1321);
x_1322 = lean_ctor_get(x_1320, 1);
lean_inc(x_1322);
lean_dec(x_1320);
x_1323 = lean_ctor_get(x_1321, 0);
lean_inc(x_1323);
x_1324 = lean_ctor_get(x_1321, 1);
lean_inc(x_1324);
if (lean_is_exclusive(x_1321)) {
 lean_ctor_release(x_1321, 0);
 lean_ctor_release(x_1321, 1);
 x_1325 = x_1321;
} else {
 lean_dec_ref(x_1321);
 x_1325 = lean_box(0);
}
lean_inc(x_1316);
if (lean_is_scalar(x_1317)) {
 x_1407 = lean_alloc_ctor(0, 2, 1);
} else {
 x_1407 = x_1317;
}
lean_ctor_set(x_1407, 0, x_1324);
lean_ctor_set(x_1407, 1, x_1316);
lean_ctor_set_uint8(x_1407, sizeof(void*)*2, x_1315);
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_1325);
lean_dec(x_1313);
lean_dec(x_1312);
lean_dec(x_4);
x_1326 = x_6;
x_1327 = x_7;
x_1328 = x_8;
x_1329 = x_9;
x_1330 = x_10;
x_1331 = x_1407;
x_1332 = x_1322;
goto block_1406;
}
else
{
lean_object* x_1408; lean_object* x_1409; 
x_1408 = lean_ctor_get(x_7, 0);
lean_inc(x_1408);
x_1409 = lean_ctor_get(x_1408, 19);
lean_inc(x_1409);
lean_dec(x_1408);
if (lean_obj_tag(x_1409) == 0)
{
lean_dec(x_1325);
lean_dec(x_1313);
lean_dec(x_1312);
lean_dec(x_4);
x_1326 = x_6;
x_1327 = x_7;
x_1328 = x_8;
x_1329 = x_9;
x_1330 = x_10;
x_1331 = x_1407;
x_1332 = x_1322;
goto block_1406;
}
else
{
lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; lean_object* x_1453; lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; uint64_t x_1458; lean_object* x_1459; lean_object* x_1460; 
x_1410 = lean_ctor_get(x_1409, 0);
lean_inc(x_1410);
lean_dec(x_1409);
x_1411 = lean_ctor_get(x_1316, 2);
lean_inc(x_1411);
x_1412 = lean_ctor_get(x_1316, 3);
lean_inc(x_1412);
x_1453 = l_Lake_instMonadWorkspaceJobM;
x_1454 = l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___redArg(x_1453, x_1312);
x_1455 = l_Lake_buildArtifactUnlessUpToDate___closed__11;
x_1456 = l_Lake_buildArtifactUnlessUpToDate___closed__12;
lean_inc(x_4);
x_1457 = l_Lake_instResolveArtifactsFileOutputHashArtifactOfMonadLakeEnvOfMonadLiftTBaseIOOfMonad___redArg(x_4, x_1454, x_1455, x_1313);
x_1458 = lean_unbox_uint64(x_1411);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1323);
lean_inc(x_6);
x_1459 = l_Lake_resolveArtifactsUsing_x3f___at___Lake_buildArtifactUnlessUpToDate_spec__0(x_1456, x_1457, x_6, x_1458, x_1323, x_1410, x_7, x_8, x_9, x_10, x_1407, x_1322);
x_1460 = lean_ctor_get(x_1459, 0);
lean_inc(x_1460);
if (lean_obj_tag(x_1460) == 0)
{
lean_object* x_1461; 
x_1461 = lean_ctor_get(x_1460, 0);
lean_inc(x_1461);
if (lean_obj_tag(x_1461) == 0)
{
lean_object* x_1462; lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; uint8_t x_1467; 
x_1462 = lean_ctor_get(x_1459, 1);
lean_inc(x_1462);
lean_dec(x_1459);
x_1463 = lean_ctor_get(x_1460, 1);
lean_inc(x_1463);
lean_dec(x_1460);
x_1464 = l_Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0(x_6, x_1, x_1316, x_1323, x_1412, x_7, x_8, x_9, x_10, x_1463, x_1462);
lean_dec(x_1412);
x_1465 = lean_ctor_get(x_1464, 0);
lean_inc(x_1465);
x_1466 = lean_ctor_get(x_1465, 0);
lean_inc(x_1466);
x_1467 = lean_unbox(x_1466);
lean_dec(x_1466);
if (x_1467 == 0)
{
lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; 
x_1468 = lean_ctor_get(x_1464, 1);
lean_inc(x_1468);
lean_dec(x_1464);
x_1469 = lean_ctor_get(x_1465, 1);
lean_inc(x_1469);
lean_dec(x_1465);
lean_inc(x_10);
lean_inc(x_1);
x_1470 = l_Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_3, x_1316, x_1319, x_6, x_7, x_8, x_9, x_10, x_1469, x_1468);
lean_dec(x_1319);
x_1471 = lean_ctor_get(x_1470, 0);
lean_inc(x_1471);
if (lean_obj_tag(x_1471) == 0)
{
lean_object* x_1472; lean_object* x_1473; 
x_1472 = lean_ctor_get(x_1470, 1);
lean_inc(x_1472);
lean_dec(x_1470);
x_1473 = lean_ctor_get(x_1471, 1);
lean_inc(x_1473);
lean_dec(x_1471);
x_1413 = x_10;
x_1414 = x_1473;
x_1415 = x_1472;
goto block_1452;
}
else
{
lean_object* x_1474; lean_object* x_1475; lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; lean_object* x_1479; lean_object* x_1480; 
lean_dec(x_1411);
lean_dec(x_1410);
lean_dec(x_1325);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_1);
x_1474 = lean_ctor_get(x_1470, 1);
lean_inc(x_1474);
if (lean_is_exclusive(x_1470)) {
 lean_ctor_release(x_1470, 0);
 lean_ctor_release(x_1470, 1);
 x_1475 = x_1470;
} else {
 lean_dec_ref(x_1470);
 x_1475 = lean_box(0);
}
x_1476 = lean_ctor_get(x_1471, 0);
lean_inc(x_1476);
x_1477 = lean_ctor_get(x_1471, 1);
lean_inc(x_1477);
if (lean_is_exclusive(x_1471)) {
 lean_ctor_release(x_1471, 0);
 lean_ctor_release(x_1471, 1);
 x_1478 = x_1471;
} else {
 lean_dec_ref(x_1471);
 x_1478 = lean_box(0);
}
if (lean_is_scalar(x_1478)) {
 x_1479 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1479 = x_1478;
}
lean_ctor_set(x_1479, 0, x_1476);
lean_ctor_set(x_1479, 1, x_1477);
if (lean_is_scalar(x_1475)) {
 x_1480 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1480 = x_1475;
}
lean_ctor_set(x_1480, 0, x_1479);
lean_ctor_set(x_1480, 1, x_1474);
return x_1480;
}
}
else
{
lean_object* x_1481; lean_object* x_1482; 
lean_dec(x_1319);
lean_dec(x_1316);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_1481 = lean_ctor_get(x_1464, 1);
lean_inc(x_1481);
lean_dec(x_1464);
x_1482 = lean_ctor_get(x_1465, 1);
lean_inc(x_1482);
lean_dec(x_1465);
x_1413 = x_10;
x_1414 = x_1482;
x_1415 = x_1481;
goto block_1452;
}
}
else
{
lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; lean_object* x_1486; lean_object* x_1487; lean_object* x_1488; lean_object* x_1500; 
lean_dec(x_1412);
lean_dec(x_1411);
lean_dec(x_1410);
lean_dec(x_1325);
lean_dec(x_1319);
lean_dec(x_1316);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1483 = lean_ctor_get(x_1459, 1);
lean_inc(x_1483);
lean_dec(x_1459);
x_1484 = lean_ctor_get(x_1460, 1);
lean_inc(x_1484);
if (lean_is_exclusive(x_1460)) {
 lean_ctor_release(x_1460, 0);
 lean_ctor_release(x_1460, 1);
 x_1485 = x_1460;
} else {
 lean_dec_ref(x_1460);
 x_1485 = lean_box(0);
}
x_1486 = lean_ctor_get(x_1461, 0);
lean_inc(x_1486);
lean_dec(x_1461);
x_1500 = l_System_FilePath_pathExists(x_1, x_1483);
if (x_5 == 0)
{
lean_object* x_1501; 
lean_dec(x_1485);
x_1501 = lean_ctor_get(x_1500, 1);
lean_inc(x_1501);
lean_dec(x_1500);
x_1487 = x_1484;
x_1488 = x_1501;
goto block_1499;
}
else
{
lean_object* x_1502; uint8_t x_1503; 
x_1502 = lean_ctor_get(x_1500, 0);
lean_inc(x_1502);
x_1503 = lean_unbox(x_1502);
lean_dec(x_1502);
if (x_1503 == 0)
{
lean_object* x_1504; lean_object* x_1505; uint8_t x_1506; lean_object* x_1507; lean_object* x_1508; lean_object* x_1509; lean_object* x_1510; lean_object* x_1511; lean_object* x_1512; lean_object* x_1513; lean_object* x_1514; uint8_t x_1515; lean_object* x_1516; lean_object* x_1517; 
x_1504 = lean_ctor_get(x_1500, 1);
lean_inc(x_1504);
lean_dec(x_1500);
x_1505 = lean_ctor_get(x_1484, 0);
lean_inc(x_1505);
x_1506 = lean_ctor_get_uint8(x_1484, sizeof(void*)*2);
x_1507 = lean_ctor_get(x_1484, 1);
lean_inc(x_1507);
if (lean_is_exclusive(x_1484)) {
 lean_ctor_release(x_1484, 0);
 lean_ctor_release(x_1484, 1);
 x_1508 = x_1484;
} else {
 lean_dec_ref(x_1484);
 x_1508 = lean_box(0);
}
x_1509 = lean_ctor_get(x_1486, 0);
lean_inc(x_1509);
x_1510 = lean_ctor_get(x_1486, 3);
lean_inc(x_1510);
x_1511 = l_Lake_buildArtifactUnlessUpToDate___closed__13;
x_1512 = lean_string_append(x_1511, x_1);
x_1513 = lean_box(0);
x_1514 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1514, 0, x_1512);
x_1515 = lean_unbox(x_1513);
lean_ctor_set_uint8(x_1514, sizeof(void*)*1, x_1515);
x_1516 = lean_array_push(x_1505, x_1514);
x_1517 = l_Lake_copyFile(x_1509, x_1, x_1504);
lean_dec(x_1509);
if (lean_obj_tag(x_1517) == 0)
{
lean_object* x_1518; uint64_t x_1519; lean_object* x_1520; 
x_1518 = lean_ctor_get(x_1517, 1);
lean_inc(x_1518);
lean_dec(x_1517);
x_1519 = lean_unbox_uint64(x_1510);
lean_dec(x_1510);
lean_inc(x_1);
x_1520 = l_Lake_writeFileHash(x_1, x_1519, x_1518);
if (lean_obj_tag(x_1520) == 0)
{
lean_object* x_1521; lean_object* x_1522; 
lean_dec(x_1485);
x_1521 = lean_ctor_get(x_1520, 1);
lean_inc(x_1521);
lean_dec(x_1520);
if (lean_is_scalar(x_1508)) {
 x_1522 = lean_alloc_ctor(0, 2, 1);
} else {
 x_1522 = x_1508;
}
lean_ctor_set(x_1522, 0, x_1516);
lean_ctor_set(x_1522, 1, x_1507);
lean_ctor_set_uint8(x_1522, sizeof(void*)*2, x_1506);
x_1487 = x_1522;
x_1488 = x_1521;
goto block_1499;
}
else
{
lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; uint8_t x_1529; lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; 
lean_dec(x_1486);
lean_dec(x_1323);
lean_dec(x_1);
x_1523 = lean_ctor_get(x_1520, 0);
lean_inc(x_1523);
x_1524 = lean_ctor_get(x_1520, 1);
lean_inc(x_1524);
if (lean_is_exclusive(x_1520)) {
 lean_ctor_release(x_1520, 0);
 lean_ctor_release(x_1520, 1);
 x_1525 = x_1520;
} else {
 lean_dec_ref(x_1520);
 x_1525 = lean_box(0);
}
x_1526 = lean_io_error_to_string(x_1523);
x_1527 = lean_box(3);
x_1528 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1528, 0, x_1526);
x_1529 = lean_unbox(x_1527);
lean_ctor_set_uint8(x_1528, sizeof(void*)*1, x_1529);
x_1530 = lean_array_get_size(x_1516);
x_1531 = lean_array_push(x_1516, x_1528);
if (lean_is_scalar(x_1508)) {
 x_1532 = lean_alloc_ctor(0, 2, 1);
} else {
 x_1532 = x_1508;
}
lean_ctor_set(x_1532, 0, x_1531);
lean_ctor_set(x_1532, 1, x_1507);
lean_ctor_set_uint8(x_1532, sizeof(void*)*2, x_1506);
if (lean_is_scalar(x_1485)) {
 x_1533 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1533 = x_1485;
 lean_ctor_set_tag(x_1533, 1);
}
lean_ctor_set(x_1533, 0, x_1530);
lean_ctor_set(x_1533, 1, x_1532);
if (lean_is_scalar(x_1525)) {
 x_1534 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1534 = x_1525;
 lean_ctor_set_tag(x_1534, 0);
}
lean_ctor_set(x_1534, 0, x_1533);
lean_ctor_set(x_1534, 1, x_1524);
return x_1534;
}
}
else
{
lean_object* x_1535; lean_object* x_1536; lean_object* x_1537; lean_object* x_1538; lean_object* x_1539; lean_object* x_1540; uint8_t x_1541; lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; lean_object* x_1545; lean_object* x_1546; 
lean_dec(x_1510);
lean_dec(x_1486);
lean_dec(x_1323);
lean_dec(x_1);
x_1535 = lean_ctor_get(x_1517, 0);
lean_inc(x_1535);
x_1536 = lean_ctor_get(x_1517, 1);
lean_inc(x_1536);
if (lean_is_exclusive(x_1517)) {
 lean_ctor_release(x_1517, 0);
 lean_ctor_release(x_1517, 1);
 x_1537 = x_1517;
} else {
 lean_dec_ref(x_1517);
 x_1537 = lean_box(0);
}
x_1538 = lean_io_error_to_string(x_1535);
x_1539 = lean_box(3);
x_1540 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1540, 0, x_1538);
x_1541 = lean_unbox(x_1539);
lean_ctor_set_uint8(x_1540, sizeof(void*)*1, x_1541);
x_1542 = lean_array_get_size(x_1516);
x_1543 = lean_array_push(x_1516, x_1540);
if (lean_is_scalar(x_1508)) {
 x_1544 = lean_alloc_ctor(0, 2, 1);
} else {
 x_1544 = x_1508;
}
lean_ctor_set(x_1544, 0, x_1543);
lean_ctor_set(x_1544, 1, x_1507);
lean_ctor_set_uint8(x_1544, sizeof(void*)*2, x_1506);
if (lean_is_scalar(x_1485)) {
 x_1545 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1545 = x_1485;
 lean_ctor_set_tag(x_1545, 1);
}
lean_ctor_set(x_1545, 0, x_1542);
lean_ctor_set(x_1545, 1, x_1544);
if (lean_is_scalar(x_1537)) {
 x_1546 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1546 = x_1537;
 lean_ctor_set_tag(x_1546, 0);
}
lean_ctor_set(x_1546, 0, x_1545);
lean_ctor_set(x_1546, 1, x_1536);
return x_1546;
}
}
else
{
lean_object* x_1547; 
lean_dec(x_1485);
x_1547 = lean_ctor_get(x_1500, 1);
lean_inc(x_1547);
lean_dec(x_1500);
x_1487 = x_1484;
x_1488 = x_1547;
goto block_1499;
}
}
block_1499:
{
lean_object* x_1489; lean_object* x_1490; lean_object* x_1491; lean_object* x_1492; lean_object* x_1493; uint8_t x_1494; lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; 
x_1489 = l_Lake_SavedTrace_replayIfExists___redArg(x_1323, x_1487, x_1488);
lean_dec(x_1323);
x_1490 = lean_ctor_get(x_1489, 0);
lean_inc(x_1490);
x_1491 = lean_ctor_get(x_1490, 1);
lean_inc(x_1491);
lean_dec(x_1490);
x_1492 = lean_ctor_get(x_1489, 1);
lean_inc(x_1492);
lean_dec(x_1489);
x_1493 = lean_ctor_get(x_1491, 0);
lean_inc(x_1493);
x_1494 = lean_ctor_get_uint8(x_1491, sizeof(void*)*2);
if (lean_is_exclusive(x_1491)) {
 lean_ctor_release(x_1491, 0);
 lean_ctor_release(x_1491, 1);
 x_1495 = x_1491;
} else {
 lean_dec_ref(x_1491);
 x_1495 = lean_box(0);
}
lean_inc(x_1486);
x_1496 = l_Lake_Artifact_trace(x_1486);
if (lean_is_scalar(x_1495)) {
 x_1497 = lean_alloc_ctor(0, 2, 1);
} else {
 x_1497 = x_1495;
}
lean_ctor_set(x_1497, 0, x_1493);
lean_ctor_set(x_1497, 1, x_1496);
lean_ctor_set_uint8(x_1497, sizeof(void*)*2, x_1494);
if (x_5 == 0)
{
lean_object* x_1498; 
lean_dec(x_1);
x_1498 = lean_ctor_get(x_1486, 0);
lean_inc(x_1498);
lean_dec(x_1486);
x_13 = x_1492;
x_14 = x_1497;
x_15 = x_1498;
goto block_18;
}
else
{
lean_dec(x_1486);
x_13 = x_1492;
x_14 = x_1497;
x_15 = x_1;
goto block_18;
}
}
}
}
else
{
lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; 
lean_dec(x_1412);
lean_dec(x_1411);
lean_dec(x_1410);
lean_dec(x_1325);
lean_dec(x_1323);
lean_dec(x_1319);
lean_dec(x_1316);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1548 = lean_ctor_get(x_1459, 1);
lean_inc(x_1548);
if (lean_is_exclusive(x_1459)) {
 lean_ctor_release(x_1459, 0);
 lean_ctor_release(x_1459, 1);
 x_1549 = x_1459;
} else {
 lean_dec_ref(x_1459);
 x_1549 = lean_box(0);
}
x_1550 = lean_ctor_get(x_1460, 0);
lean_inc(x_1550);
x_1551 = lean_ctor_get(x_1460, 1);
lean_inc(x_1551);
if (lean_is_exclusive(x_1460)) {
 lean_ctor_release(x_1460, 0);
 lean_ctor_release(x_1460, 1);
 x_1552 = x_1460;
} else {
 lean_dec_ref(x_1460);
 x_1552 = lean_box(0);
}
if (lean_is_scalar(x_1552)) {
 x_1553 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1553 = x_1552;
}
lean_ctor_set(x_1553, 0, x_1550);
lean_ctor_set(x_1553, 1, x_1551);
if (lean_is_scalar(x_1549)) {
 x_1554 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1554 = x_1549;
}
lean_ctor_set(x_1554, 0, x_1553);
lean_ctor_set(x_1554, 1, x_1548);
return x_1554;
}
block_1452:
{
lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; uint8_t x_1419; lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; lean_object* x_1423; 
x_1416 = lean_ctor_get(x_1413, 1);
lean_inc(x_1416);
lean_dec(x_1413);
x_1417 = lean_ctor_get(x_1416, 1);
lean_inc(x_1417);
lean_dec(x_1416);
x_1418 = lean_ctor_get(x_1414, 0);
lean_inc(x_1418);
x_1419 = lean_ctor_get_uint8(x_1414, sizeof(void*)*2);
x_1420 = lean_ctor_get(x_1414, 1);
lean_inc(x_1420);
if (lean_is_exclusive(x_1414)) {
 lean_ctor_release(x_1414, 0);
 lean_ctor_release(x_1414, 1);
 x_1421 = x_1414;
} else {
 lean_dec_ref(x_1414);
 x_1421 = lean_box(0);
}
x_1422 = lean_ctor_get(x_1417, 6);
lean_inc(x_1422);
lean_dec(x_1417);
lean_inc(x_1);
x_1423 = l_Lake_Cache_saveArtifact(x_1422, x_1, x_4, x_3, x_1415);
lean_dec(x_4);
if (lean_obj_tag(x_1423) == 0)
{
lean_object* x_1424; lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; lean_object* x_1430; uint64_t x_1431; lean_object* x_1432; lean_object* x_1433; uint64_t x_1434; lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; 
lean_dec(x_1420);
lean_dec(x_1325);
x_1424 = lean_ctor_get(x_1423, 0);
lean_inc(x_1424);
x_1425 = lean_ctor_get(x_1423, 1);
lean_inc(x_1425);
lean_dec(x_1423);
x_1426 = lean_st_ref_take(x_1410, x_1425);
x_1427 = lean_ctor_get(x_1426, 0);
lean_inc(x_1427);
x_1428 = lean_ctor_get(x_1426, 1);
lean_inc(x_1428);
lean_dec(x_1426);
x_1429 = lean_ctor_get(x_1424, 0);
lean_inc(x_1429);
x_1430 = lean_ctor_get(x_1424, 3);
lean_inc(x_1430);
x_1431 = lean_unbox_uint64(x_1430);
lean_dec(x_1430);
x_1432 = lean_uint64_to_nat(x_1431);
x_1433 = l_Lean_bignumToJson(x_1432);
x_1434 = lean_unbox_uint64(x_1411);
lean_dec(x_1411);
x_1435 = l_Lake_CacheMap_insertCore(x_1434, x_1433, x_1427);
x_1436 = lean_st_ref_set(x_1410, x_1435, x_1428);
lean_dec(x_1410);
x_1437 = lean_ctor_get(x_1436, 1);
lean_inc(x_1437);
lean_dec(x_1436);
x_1438 = l_Lake_Artifact_trace(x_1424);
if (lean_is_scalar(x_1421)) {
 x_1439 = lean_alloc_ctor(0, 2, 1);
} else {
 x_1439 = x_1421;
}
lean_ctor_set(x_1439, 0, x_1418);
lean_ctor_set(x_1439, 1, x_1438);
lean_ctor_set_uint8(x_1439, sizeof(void*)*2, x_1419);
if (x_5 == 0)
{
lean_dec(x_1);
x_19 = x_1437;
x_20 = x_1439;
x_21 = x_1429;
goto block_24;
}
else
{
lean_dec(x_1429);
x_19 = x_1437;
x_20 = x_1439;
x_21 = x_1;
goto block_24;
}
}
else
{
lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; uint8_t x_1446; lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; 
lean_dec(x_1411);
lean_dec(x_1410);
lean_dec(x_1);
x_1440 = lean_ctor_get(x_1423, 0);
lean_inc(x_1440);
x_1441 = lean_ctor_get(x_1423, 1);
lean_inc(x_1441);
if (lean_is_exclusive(x_1423)) {
 lean_ctor_release(x_1423, 0);
 lean_ctor_release(x_1423, 1);
 x_1442 = x_1423;
} else {
 lean_dec_ref(x_1423);
 x_1442 = lean_box(0);
}
x_1443 = lean_io_error_to_string(x_1440);
x_1444 = lean_box(3);
x_1445 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1445, 0, x_1443);
x_1446 = lean_unbox(x_1444);
lean_ctor_set_uint8(x_1445, sizeof(void*)*1, x_1446);
x_1447 = lean_array_get_size(x_1418);
x_1448 = lean_array_push(x_1418, x_1445);
if (lean_is_scalar(x_1421)) {
 x_1449 = lean_alloc_ctor(0, 2, 1);
} else {
 x_1449 = x_1421;
}
lean_ctor_set(x_1449, 0, x_1448);
lean_ctor_set(x_1449, 1, x_1420);
lean_ctor_set_uint8(x_1449, sizeof(void*)*2, x_1419);
if (lean_is_scalar(x_1325)) {
 x_1450 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1450 = x_1325;
 lean_ctor_set_tag(x_1450, 1);
}
lean_ctor_set(x_1450, 0, x_1447);
lean_ctor_set(x_1450, 1, x_1449);
if (lean_is_scalar(x_1442)) {
 x_1451 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1451 = x_1442;
 lean_ctor_set_tag(x_1451, 0);
}
lean_ctor_set(x_1451, 0, x_1450);
lean_ctor_set(x_1451, 1, x_1441);
return x_1451;
}
}
}
}
block_1406:
{
lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; uint8_t x_1337; 
x_1333 = lean_ctor_get(x_1316, 3);
lean_inc(x_1333);
x_1334 = l_Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0(x_1326, x_1, x_1316, x_1323, x_1333, x_1327, x_1328, x_1329, x_1330, x_1331, x_1332);
lean_dec(x_1333);
x_1335 = lean_ctor_get(x_1334, 0);
lean_inc(x_1335);
x_1336 = lean_ctor_get(x_1335, 0);
lean_inc(x_1336);
x_1337 = lean_unbox(x_1336);
lean_dec(x_1336);
if (x_1337 == 0)
{
lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; 
x_1338 = lean_ctor_get(x_1334, 1);
lean_inc(x_1338);
lean_dec(x_1334);
x_1339 = lean_ctor_get(x_1335, 1);
lean_inc(x_1339);
lean_dec(x_1335);
lean_inc(x_1);
x_1340 = l_Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_3, x_1316, x_1319, x_1326, x_1327, x_1328, x_1329, x_1330, x_1339, x_1338);
lean_dec(x_1319);
x_1341 = lean_ctor_get(x_1340, 0);
lean_inc(x_1341);
if (lean_obj_tag(x_1341) == 0)
{
lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; uint8_t x_1347; lean_object* x_1348; lean_object* x_1349; uint64_t x_1350; lean_object* x_1351; 
x_1342 = lean_ctor_get(x_1341, 1);
lean_inc(x_1342);
x_1343 = lean_ctor_get(x_1340, 1);
lean_inc(x_1343);
lean_dec(x_1340);
x_1344 = lean_ctor_get(x_1341, 0);
lean_inc(x_1344);
if (lean_is_exclusive(x_1341)) {
 lean_ctor_release(x_1341, 0);
 lean_ctor_release(x_1341, 1);
 x_1345 = x_1341;
} else {
 lean_dec_ref(x_1341);
 x_1345 = lean_box(0);
}
x_1346 = lean_ctor_get(x_1342, 0);
lean_inc(x_1346);
x_1347 = lean_ctor_get_uint8(x_1342, sizeof(void*)*2);
x_1348 = lean_ctor_get(x_1342, 1);
lean_inc(x_1348);
if (lean_is_exclusive(x_1342)) {
 lean_ctor_release(x_1342, 0);
 lean_ctor_release(x_1342, 1);
 x_1349 = x_1342;
} else {
 lean_dec_ref(x_1342);
 x_1349 = lean_box(0);
}
x_1350 = lean_unbox_uint64(x_1344);
lean_inc(x_1);
x_1351 = l_Lake_writeFileHash(x_1, x_1350, x_1343);
if (lean_obj_tag(x_1351) == 0)
{
lean_object* x_1352; uint64_t x_1353; lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; 
lean_dec(x_1348);
x_1352 = lean_ctor_get(x_1351, 1);
lean_inc(x_1352);
lean_dec(x_1351);
x_1353 = lean_unbox_uint64(x_1344);
lean_dec(x_1344);
lean_inc(x_1);
x_1354 = l_Lake_computeArtifactTrace(x_1, x_1, x_1353, x_1352);
x_1355 = lean_ctor_get(x_1354, 0);
lean_inc(x_1355);
x_1356 = lean_ctor_get(x_1354, 1);
lean_inc(x_1356);
if (lean_is_exclusive(x_1354)) {
 lean_ctor_release(x_1354, 0);
 lean_ctor_release(x_1354, 1);
 x_1357 = x_1354;
} else {
 lean_dec_ref(x_1354);
 x_1357 = lean_box(0);
}
if (lean_is_scalar(x_1349)) {
 x_1358 = lean_alloc_ctor(0, 2, 1);
} else {
 x_1358 = x_1349;
}
lean_ctor_set(x_1358, 0, x_1346);
lean_ctor_set(x_1358, 1, x_1355);
lean_ctor_set_uint8(x_1358, sizeof(void*)*2, x_1347);
if (lean_is_scalar(x_1345)) {
 x_1359 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1359 = x_1345;
}
lean_ctor_set(x_1359, 0, x_1);
lean_ctor_set(x_1359, 1, x_1358);
if (lean_is_scalar(x_1357)) {
 x_1360 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1360 = x_1357;
}
lean_ctor_set(x_1360, 0, x_1359);
lean_ctor_set(x_1360, 1, x_1356);
return x_1360;
}
else
{
lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; uint8_t x_1367; lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; 
lean_dec(x_1344);
lean_dec(x_1);
x_1361 = lean_ctor_get(x_1351, 0);
lean_inc(x_1361);
x_1362 = lean_ctor_get(x_1351, 1);
lean_inc(x_1362);
if (lean_is_exclusive(x_1351)) {
 lean_ctor_release(x_1351, 0);
 lean_ctor_release(x_1351, 1);
 x_1363 = x_1351;
} else {
 lean_dec_ref(x_1351);
 x_1363 = lean_box(0);
}
x_1364 = lean_io_error_to_string(x_1361);
x_1365 = lean_box(3);
x_1366 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1366, 0, x_1364);
x_1367 = lean_unbox(x_1365);
lean_ctor_set_uint8(x_1366, sizeof(void*)*1, x_1367);
x_1368 = lean_array_get_size(x_1346);
x_1369 = lean_array_push(x_1346, x_1366);
if (lean_is_scalar(x_1349)) {
 x_1370 = lean_alloc_ctor(0, 2, 1);
} else {
 x_1370 = x_1349;
}
lean_ctor_set(x_1370, 0, x_1369);
lean_ctor_set(x_1370, 1, x_1348);
lean_ctor_set_uint8(x_1370, sizeof(void*)*2, x_1347);
if (lean_is_scalar(x_1345)) {
 x_1371 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1371 = x_1345;
 lean_ctor_set_tag(x_1371, 1);
}
lean_ctor_set(x_1371, 0, x_1368);
lean_ctor_set(x_1371, 1, x_1370);
if (lean_is_scalar(x_1363)) {
 x_1372 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1372 = x_1363;
 lean_ctor_set_tag(x_1372, 0);
}
lean_ctor_set(x_1372, 0, x_1371);
lean_ctor_set(x_1372, 1, x_1362);
return x_1372;
}
}
else
{
lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; 
lean_dec(x_1);
x_1373 = lean_ctor_get(x_1340, 1);
lean_inc(x_1373);
if (lean_is_exclusive(x_1340)) {
 lean_ctor_release(x_1340, 0);
 lean_ctor_release(x_1340, 1);
 x_1374 = x_1340;
} else {
 lean_dec_ref(x_1340);
 x_1374 = lean_box(0);
}
x_1375 = lean_ctor_get(x_1341, 0);
lean_inc(x_1375);
x_1376 = lean_ctor_get(x_1341, 1);
lean_inc(x_1376);
if (lean_is_exclusive(x_1341)) {
 lean_ctor_release(x_1341, 0);
 lean_ctor_release(x_1341, 1);
 x_1377 = x_1341;
} else {
 lean_dec_ref(x_1341);
 x_1377 = lean_box(0);
}
if (lean_is_scalar(x_1377)) {
 x_1378 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1378 = x_1377;
}
lean_ctor_set(x_1378, 0, x_1375);
lean_ctor_set(x_1378, 1, x_1376);
if (lean_is_scalar(x_1374)) {
 x_1379 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1379 = x_1374;
}
lean_ctor_set(x_1379, 0, x_1378);
lean_ctor_set(x_1379, 1, x_1373);
return x_1379;
}
}
else
{
lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; 
lean_dec(x_1329);
lean_dec(x_1328);
lean_dec(x_1327);
lean_dec(x_1326);
lean_dec(x_1319);
lean_dec(x_1316);
lean_dec(x_2);
x_1380 = lean_ctor_get(x_1334, 1);
lean_inc(x_1380);
lean_dec(x_1334);
x_1381 = lean_ctor_get(x_1335, 1);
lean_inc(x_1381);
lean_dec(x_1335);
lean_inc(x_1);
x_1382 = l_Lake_fetchFileHash___redArg(x_1, x_3, x_1330, x_1381, x_1380);
lean_dec(x_1330);
x_1383 = lean_ctor_get(x_1382, 0);
lean_inc(x_1383);
if (lean_obj_tag(x_1383) == 0)
{
lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; uint64_t x_1388; lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; uint8_t x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; 
x_1384 = lean_ctor_get(x_1382, 1);
lean_inc(x_1384);
lean_dec(x_1382);
x_1385 = lean_ctor_get(x_1383, 0);
lean_inc(x_1385);
x_1386 = lean_ctor_get(x_1383, 1);
lean_inc(x_1386);
if (lean_is_exclusive(x_1383)) {
 lean_ctor_release(x_1383, 0);
 lean_ctor_release(x_1383, 1);
 x_1387 = x_1383;
} else {
 lean_dec_ref(x_1383);
 x_1387 = lean_box(0);
}
x_1388 = lean_unbox_uint64(x_1385);
lean_dec(x_1385);
lean_inc(x_1);
x_1389 = l_Lake_computeArtifactTrace(x_1, x_1, x_1388, x_1384);
x_1390 = lean_ctor_get(x_1389, 0);
lean_inc(x_1390);
x_1391 = lean_ctor_get(x_1389, 1);
lean_inc(x_1391);
if (lean_is_exclusive(x_1389)) {
 lean_ctor_release(x_1389, 0);
 lean_ctor_release(x_1389, 1);
 x_1392 = x_1389;
} else {
 lean_dec_ref(x_1389);
 x_1392 = lean_box(0);
}
x_1393 = lean_ctor_get(x_1386, 0);
lean_inc(x_1393);
x_1394 = lean_ctor_get_uint8(x_1386, sizeof(void*)*2);
if (lean_is_exclusive(x_1386)) {
 lean_ctor_release(x_1386, 0);
 lean_ctor_release(x_1386, 1);
 x_1395 = x_1386;
} else {
 lean_dec_ref(x_1386);
 x_1395 = lean_box(0);
}
if (lean_is_scalar(x_1395)) {
 x_1396 = lean_alloc_ctor(0, 2, 1);
} else {
 x_1396 = x_1395;
}
lean_ctor_set(x_1396, 0, x_1393);
lean_ctor_set(x_1396, 1, x_1390);
lean_ctor_set_uint8(x_1396, sizeof(void*)*2, x_1394);
if (lean_is_scalar(x_1387)) {
 x_1397 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1397 = x_1387;
}
lean_ctor_set(x_1397, 0, x_1);
lean_ctor_set(x_1397, 1, x_1396);
if (lean_is_scalar(x_1392)) {
 x_1398 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1398 = x_1392;
}
lean_ctor_set(x_1398, 0, x_1397);
lean_ctor_set(x_1398, 1, x_1391);
return x_1398;
}
else
{
lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; 
lean_dec(x_1);
x_1399 = lean_ctor_get(x_1382, 1);
lean_inc(x_1399);
if (lean_is_exclusive(x_1382)) {
 lean_ctor_release(x_1382, 0);
 lean_ctor_release(x_1382, 1);
 x_1400 = x_1382;
} else {
 lean_dec_ref(x_1382);
 x_1400 = lean_box(0);
}
x_1401 = lean_ctor_get(x_1383, 0);
lean_inc(x_1401);
x_1402 = lean_ctor_get(x_1383, 1);
lean_inc(x_1402);
if (lean_is_exclusive(x_1383)) {
 lean_ctor_release(x_1383, 0);
 lean_ctor_release(x_1383, 1);
 x_1403 = x_1383;
} else {
 lean_dec_ref(x_1383);
 x_1403 = lean_box(0);
}
if (lean_is_scalar(x_1403)) {
 x_1404 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1404 = x_1403;
}
lean_ctor_set(x_1404, 0, x_1401);
lean_ctor_set(x_1404, 1, x_1402);
if (lean_is_scalar(x_1400)) {
 x_1405 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1405 = x_1400;
}
lean_ctor_set(x_1405, 0, x_1404);
lean_ctor_set(x_1405, 1, x_1399);
return x_1405;
}
}
}
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
block_24:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifactsUsing_x3f___at___Lake_buildArtifactUnlessUpToDate_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint64_t x_13; lean_object* x_14; 
x_13 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_14 = l_Lake_resolveArtifactsUsing_x3f___at___Lake_buildArtifactUnlessUpToDate_spec__0(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Lake_buildArtifactUnlessUpToDate(x_1, x_2, x_13, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
static lean_object* _init_l_Lake_buildFileAfterDep___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("art", 3, 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_13 = lean_apply_7(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_15, 1);
x_20 = l_Lake_BuildTrace_mix(x_19, x_17);
lean_ctor_set(x_15, 1, x_20);
x_21 = lean_apply_1(x_2, x_5);
x_22 = l_Lake_buildFileAfterDep___redArg___lam__0___closed__0;
x_23 = lean_box(0);
x_24 = lean_unbox(x_23);
x_25 = l_Lake_buildArtifactUnlessUpToDate(x_3, x_21, x_4, x_22, x_24, x_6, x_7, x_8, x_9, x_10, x_15, x_16);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_inc(x_26);
lean_dec(x_15);
x_29 = l_Lake_BuildTrace_mix(x_28, x_17);
x_30 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_27);
x_31 = lean_apply_1(x_2, x_5);
x_32 = l_Lake_buildFileAfterDep___redArg___lam__0___closed__0;
x_33 = lean_box(0);
x_34 = lean_unbox(x_33);
x_35 = l_Lake_buildArtifactUnlessUpToDate(x_3, x_31, x_4, x_32, x_34, x_6, x_7, x_8, x_9, x_10, x_30, x_16);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_13);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_13, 0);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_14);
if (x_38 == 0)
{
return x_13;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_14, 0);
x_40 = lean_ctor_get(x_14, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_14);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_13, 0, x_41);
return x_13;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_13, 1);
lean_inc(x_42);
lean_dec(x_13);
x_43 = lean_ctor_get(x_14, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_14, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_45 = x_14;
} else {
 lean_dec_ref(x_14);
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
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_13 = lean_box(x_5);
x_14 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___redArg___lam__0___boxed), 12, 4);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_3);
lean_closure_set(x_14, 2, x_1);
lean_closure_set(x_14, 3, x_13);
x_15 = l_Lake_instDataKindFilePath;
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
x_19 = l_Lake_Job_mapM___redArg(x_15, x_2, x_14, x_16, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_14 = lean_box(x_6);
x_15 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___redArg___lam__0___boxed), 12, 4);
lean_closure_set(x_15, 0, x_5);
lean_closure_set(x_15, 1, x_4);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_14);
x_16 = l_Lake_instDataKindFilePath;
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
x_20 = l_Lake_Job_mapM___redArg(x_16, x_3, x_15, x_17, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l_Lake_buildFileAfterDep___redArg___lam__0(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Lake_buildFileAfterDep___redArg(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_6);
lean_dec(x_6);
x_15 = l_Lake_buildFileAfterDep(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepList___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_13 = lean_apply_7(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_15, 1);
x_20 = l_Lake_BuildTrace_mix(x_19, x_17);
lean_ctor_set(x_15, 1, x_20);
x_21 = lean_apply_1(x_2, x_5);
x_22 = l_Lake_buildFileAfterDep___redArg___lam__0___closed__0;
x_23 = lean_box(0);
x_24 = lean_unbox(x_23);
x_25 = l_Lake_buildArtifactUnlessUpToDate(x_3, x_21, x_4, x_22, x_24, x_6, x_7, x_8, x_9, x_10, x_15, x_16);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_inc(x_26);
lean_dec(x_15);
x_29 = l_Lake_BuildTrace_mix(x_28, x_17);
x_30 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_27);
x_31 = lean_apply_1(x_2, x_5);
x_32 = l_Lake_buildFileAfterDep___redArg___lam__0___closed__0;
x_33 = lean_box(0);
x_34 = lean_unbox(x_33);
x_35 = l_Lake_buildArtifactUnlessUpToDate(x_3, x_31, x_4, x_32, x_34, x_6, x_7, x_8, x_9, x_10, x_30, x_16);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_13);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_13, 0);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_14);
if (x_38 == 0)
{
return x_13;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_14, 0);
x_40 = lean_ctor_get(x_14, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_14);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_13, 0, x_41);
return x_13;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_13, 1);
lean_inc(x_42);
lean_dec(x_13);
x_43 = lean_ctor_get(x_14, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_14, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_45 = x_14;
} else {
 lean_dec_ref(x_14);
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
static lean_object* _init_l_Lake_buildFileAfterDepList___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<collection>", 12, 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepList___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_13 = lean_box(x_5);
x_14 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDepList___redArg___lam__0___boxed), 12, 4);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_3);
lean_closure_set(x_14, 2, x_1);
lean_closure_set(x_14, 3, x_13);
x_15 = l_Lake_buildFileAfterDepList___redArg___closed__0;
x_16 = l_Lake_Job_collectList___redArg(x_2, x_15);
x_17 = l_Lake_instDataKindFilePath;
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
x_21 = l_Lake_Job_mapM___redArg(x_17, x_16, x_14, x_18, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepList(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_14 = lean_box(x_6);
x_15 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDepList___redArg___lam__0___boxed), 12, 4);
lean_closure_set(x_15, 0, x_5);
lean_closure_set(x_15, 1, x_4);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_14);
x_16 = l_Lake_buildFileAfterDepList___redArg___closed__0;
x_17 = l_Lake_Job_collectList___redArg(x_3, x_16);
x_18 = l_Lake_instDataKindFilePath;
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_box(0);
x_21 = lean_unbox(x_20);
x_22 = l_Lake_Job_mapM___redArg(x_18, x_17, x_15, x_19, x_21, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepList___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l_Lake_buildFileAfterDepList___redArg___lam__0(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepList___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Lake_buildFileAfterDepList___redArg(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepList___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_6);
lean_dec(x_6);
x_15 = l_Lake_buildFileAfterDepList(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepArray___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_13 = lean_apply_7(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_15, 1);
x_20 = l_Lake_BuildTrace_mix(x_19, x_17);
lean_ctor_set(x_15, 1, x_20);
x_21 = lean_apply_1(x_2, x_5);
x_22 = l_Lake_buildFileAfterDep___redArg___lam__0___closed__0;
x_23 = lean_box(0);
x_24 = lean_unbox(x_23);
x_25 = l_Lake_buildArtifactUnlessUpToDate(x_3, x_21, x_4, x_22, x_24, x_6, x_7, x_8, x_9, x_10, x_15, x_16);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_inc(x_26);
lean_dec(x_15);
x_29 = l_Lake_BuildTrace_mix(x_28, x_17);
x_30 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_27);
x_31 = lean_apply_1(x_2, x_5);
x_32 = l_Lake_buildFileAfterDep___redArg___lam__0___closed__0;
x_33 = lean_box(0);
x_34 = lean_unbox(x_33);
x_35 = l_Lake_buildArtifactUnlessUpToDate(x_3, x_31, x_4, x_32, x_34, x_6, x_7, x_8, x_9, x_10, x_30, x_16);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_13);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_13, 0);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_14);
if (x_38 == 0)
{
return x_13;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_14, 0);
x_40 = lean_ctor_get(x_14, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_14);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_13, 0, x_41);
return x_13;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_13, 1);
lean_inc(x_42);
lean_dec(x_13);
x_43 = lean_ctor_get(x_14, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_14, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_45 = x_14;
} else {
 lean_dec_ref(x_14);
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
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepArray___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_13 = lean_box(x_5);
x_14 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDepArray___redArg___lam__0___boxed), 12, 4);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_3);
lean_closure_set(x_14, 2, x_1);
lean_closure_set(x_14, 3, x_13);
x_15 = l_Lake_buildFileAfterDepList___redArg___closed__0;
x_16 = l_Lake_Job_collectArray___redArg(x_2, x_15);
x_17 = l_Lake_instDataKindFilePath;
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
x_21 = l_Lake_Job_mapM___redArg(x_17, x_16, x_14, x_18, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepArray(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_14 = lean_box(x_6);
x_15 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDepArray___redArg___lam__0___boxed), 12, 4);
lean_closure_set(x_15, 0, x_5);
lean_closure_set(x_15, 1, x_4);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_14);
x_16 = l_Lake_buildFileAfterDepList___redArg___closed__0;
x_17 = l_Lake_Job_collectArray___redArg(x_3, x_16);
x_18 = l_Lake_instDataKindFilePath;
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_box(0);
x_21 = lean_unbox(x_20);
x_22 = l_Lake_Job_mapM___redArg(x_18, x_17, x_15, x_19, x_21, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepArray___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l_Lake_buildFileAfterDepArray___redArg___lam__0(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepArray___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Lake_buildFileAfterDepArray___redArg(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepArray___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_6);
lean_dec(x_6);
x_15 = l_Lake_buildFileAfterDepArray(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___Lake_inputBinFile_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_computeBinFileHash(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_io_metadata(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lake_platformTrace___closed__2;
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_11, 2, x_4);
lean_ctor_set(x_11, 3, x_9);
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lake_platformTrace___closed__2;
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_4);
lean_ctor_set(x_16, 3, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_4);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_6);
if (x_18 == 0)
{
return x_6;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_6, 0);
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_6);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_3);
if (x_22 == 0)
{
return x_3;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_3, 0);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_3);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_get_set_stdout(x_1, x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(0);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
lean_inc(x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
x_26 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1___redArg___lam__0(x_17, x_22, x_25, x_24, x_21);
lean_dec(x_25);
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
lean_dec(x_20);
x_41 = lean_box(0);
x_42 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1___redArg___lam__0(x_17, x_22, x_41, x_40, x_21);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
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
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_get_set_stdin(x_1, x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(0);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
lean_inc(x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
x_26 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2___redArg___lam__0(x_17, x_22, x_25, x_24, x_21);
lean_dec(x_25);
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
lean_dec(x_20);
x_41 = lean_box(0);
x_42 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2___redArg___lam__0(x_17, x_22, x_41, x_40, x_21);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
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
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__3___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_get_set_stderr(x_1, x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(0);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
lean_inc(x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
x_26 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__3___redArg___lam__0(x_17, x_22, x_25, x_24, x_21);
lean_dec(x_25);
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
lean_dec(x_20);
x_41 = lean_box(0);
x_42 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__3___redArg___lam__0(x_17, x_22, x_41, x_40, x_21);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
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
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__0() {
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
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.String.Extra", 22, 22);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String.fromUTF8!", 16, 16);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid UTF-8 string", 20, 20);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__3;
x_2 = lean_unsigned_to_nat(47u);
x_3 = lean_unsigned_to_nat(129u);
x_4 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__2;
x_5 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__1;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__0;
x_19 = lean_st_mk_ref(x_18, x_9);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_st_mk_ref(x_18, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
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
lean_inc(x_26);
x_55 = lean_alloc_closure((void*)(l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__3), 10, 3);
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
x_28 = lean_alloc_closure((void*)(l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1), 10, 3);
lean_closure_set(x_28, 0, lean_box(0));
lean_closure_set(x_28, 1, x_26);
lean_closure_set(x_28, 2, x_27);
x_29 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2___redArg(x_25, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_st_ref_get(x_23, x_31);
lean_dec(x_23);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_string_validate_utf8(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_37);
x_39 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__4;
x_40 = l_panic___at___Lean_Name_getString_x21_spec__0(x_39);
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
lean_dec(x_37);
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
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_1);
x_12 = l_Lake_BuildTrace_compute___at___Lake_inputBinFile_spec__0(x_1, x_8);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_7, 1, x_14);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_7);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
lean_ctor_set(x_7, 1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_7);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_io_error_to_string(x_21);
x_23 = lean_box(3);
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_22);
x_25 = lean_unbox(x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_25);
x_26 = lean_array_get_size(x_10);
x_27 = lean_array_push(x_10, x_24);
lean_ctor_set(x_7, 0, x_27);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_7);
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_28);
return x_12;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_12, 0);
x_30 = lean_ctor_get(x_12, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_12);
x_31 = lean_io_error_to_string(x_29);
x_32 = lean_box(3);
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_31);
x_34 = lean_unbox(x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_34);
x_35 = lean_array_get_size(x_10);
x_36 = lean_array_push(x_10, x_33);
lean_ctor_set(x_7, 0, x_36);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_7);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_30);
return x_38;
}
}
}
else
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_7, 0);
x_40 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_41 = lean_ctor_get(x_7, 1);
lean_inc(x_41);
lean_inc(x_39);
lean_dec(x_7);
lean_inc(x_1);
x_42 = l_Lake_BuildTrace_compute___at___Lake_inputBinFile_spec__0(x_1, x_8);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
x_46 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set(x_46, 1, x_43);
lean_ctor_set_uint8(x_46, sizeof(void*)*2, x_40);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_46);
if (lean_is_scalar(x_45)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_45;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_1);
x_49 = lean_ctor_get(x_42, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_42, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_51 = x_42;
} else {
 lean_dec_ref(x_42);
 x_51 = lean_box(0);
}
x_52 = lean_io_error_to_string(x_49);
x_53 = lean_box(3);
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_52);
x_55 = lean_unbox(x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_55);
x_56 = lean_array_get_size(x_39);
x_57 = lean_array_push(x_39, x_54);
x_58 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_41);
lean_ctor_set_uint8(x_58, sizeof(void*)*2, x_40);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_58);
if (lean_is_scalar(x_51)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_51;
 lean_ctor_set_tag(x_60, 0);
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_50);
return x_60;
}
}
}
}
static lean_object* _init_l_Lake_inputBinFile___redArg___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stdout/stderr:\n", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10);
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
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_30 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_18, x_25, x_9);
x_31 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_18, x_30, x_25);
x_32 = lean_string_utf8_extract(x_18, x_30, x_31);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_18);
x_33 = lean_string_append(x_29, x_32);
lean_dec(x_32);
x_34 = lean_box(1);
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
x_36 = lean_unbox(x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_36);
x_37 = lean_array_push(x_28, x_35);
lean_ctor_set(x_16, 0, x_37);
x_20 = x_16;
x_21 = x_14;
goto block_24;
}
else
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_38 = lean_ctor_get(x_16, 0);
x_39 = lean_ctor_get_uint8(x_16, sizeof(void*)*2);
x_40 = lean_ctor_get(x_16, 1);
lean_inc(x_40);
lean_inc(x_38);
lean_dec(x_16);
x_41 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_42 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_18, x_25, x_9);
x_43 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_18, x_42, x_25);
x_44 = lean_string_utf8_extract(x_18, x_42, x_43);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_18);
x_45 = lean_string_append(x_41, x_44);
lean_dec(x_44);
x_46 = lean_box(1);
x_47 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_47, 0, x_45);
x_48 = lean_unbox(x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_48);
x_49 = lean_array_push(x_38, x_47);
x_50 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_40);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_39);
x_20 = x_50;
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
uint8_t x_51; 
lean_dec(x_9);
x_51 = !lean_is_exclusive(x_11);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_11, 0);
lean_dec(x_52);
x_53 = !lean_is_exclusive(x_12);
if (x_53 == 0)
{
return x_11;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_12, 0);
x_55 = lean_ctor_get(x_12, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_12);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_11, 0, x_56);
return x_11;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_11, 1);
lean_inc(x_57);
lean_dec(x_11);
x_58 = lean_ctor_get(x_12, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_12, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_60 = x_12;
} else {
 lean_dec_ref(x_12);
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
static lean_object* _init_l_Lake_inputBinFile___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<nil>", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_inputBinFile___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_inputBinFile___redArg___closed__0;
x_2 = l_Lake_BuildTrace_nil(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_inputBinFile___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_1 = l_Lake_inputBinFile___redArg___closed__1;
x_2 = lean_box(0);
x_3 = l_Lake_BuildMetadata_fromJson_x3f___closed__3;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
x_5 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_5);
return x_4;
}
}
static lean_object* _init_l_Lake_inputBinFile___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_alloc_closure((void*)(l_Lake_inputBinFile___redArg___lam__0___boxed), 8, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lake_inputBinFile___redArg___closed__2;
x_11 = lean_box(1);
x_12 = lean_alloc_closure((void*)(l_Lake_inputBinFile___redArg___lam__1___boxed), 10, 9);
lean_closure_set(x_12, 0, x_8);
lean_closure_set(x_12, 1, x_11);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_3);
lean_closure_set(x_12, 4, x_4);
lean_closure_set(x_12, 5, x_5);
lean_closure_set(x_12, 6, x_6);
lean_closure_set(x_12, 7, x_10);
lean_closure_set(x_12, 8, x_9);
x_13 = lean_io_as_task(x_12, x_9, x_7);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lake_instDataKindFilePath;
x_17 = l_Lake_inputBinFile___redArg___closed__3;
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_17);
x_20 = lean_unbox(x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*3, x_20);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_23 = l_Lake_instDataKindFilePath;
x_24 = l_Lake_inputBinFile___redArg___closed__3;
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set(x_26, 2, x_24);
x_27 = lean_unbox(x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*3, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_22);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_inputBinFile___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__3___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__3___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_inputBinFile___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lake_inputBinFile___redArg___lam__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_inputBinFile(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___Lake_inputTextFile_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_computeTextFileHash(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_io_metadata(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lake_platformTrace___closed__2;
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_11, 2, x_4);
lean_ctor_set(x_11, 3, x_9);
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lake_platformTrace___closed__2;
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_4);
lean_ctor_set(x_16, 3, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_4);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_6);
if (x_18 == 0)
{
return x_6;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_6, 0);
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_6);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_3);
if (x_22 == 0)
{
return x_3;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_3, 0);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_3);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_1);
x_12 = l_Lake_BuildTrace_compute___at___Lake_inputTextFile_spec__0(x_1, x_8);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_7, 1, x_14);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_7);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
lean_ctor_set(x_7, 1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_7);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_io_error_to_string(x_21);
x_23 = lean_box(3);
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_22);
x_25 = lean_unbox(x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_25);
x_26 = lean_array_get_size(x_10);
x_27 = lean_array_push(x_10, x_24);
lean_ctor_set(x_7, 0, x_27);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_7);
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_28);
return x_12;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_12, 0);
x_30 = lean_ctor_get(x_12, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_12);
x_31 = lean_io_error_to_string(x_29);
x_32 = lean_box(3);
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_31);
x_34 = lean_unbox(x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_34);
x_35 = lean_array_get_size(x_10);
x_36 = lean_array_push(x_10, x_33);
lean_ctor_set(x_7, 0, x_36);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_7);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_30);
return x_38;
}
}
}
else
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_7, 0);
x_40 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_41 = lean_ctor_get(x_7, 1);
lean_inc(x_41);
lean_inc(x_39);
lean_dec(x_7);
lean_inc(x_1);
x_42 = l_Lake_BuildTrace_compute___at___Lake_inputTextFile_spec__0(x_1, x_8);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
x_46 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set(x_46, 1, x_43);
lean_ctor_set_uint8(x_46, sizeof(void*)*2, x_40);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_46);
if (lean_is_scalar(x_45)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_45;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_1);
x_49 = lean_ctor_get(x_42, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_42, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_51 = x_42;
} else {
 lean_dec_ref(x_42);
 x_51 = lean_box(0);
}
x_52 = lean_io_error_to_string(x_49);
x_53 = lean_box(3);
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_52);
x_55 = lean_unbox(x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_55);
x_56 = lean_array_get_size(x_39);
x_57 = lean_array_push(x_39, x_54);
x_58 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_41);
lean_ctor_set_uint8(x_58, sizeof(void*)*2, x_40);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_58);
if (lean_is_scalar(x_51)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_51;
 lean_ctor_set_tag(x_60, 0);
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_50);
return x_60;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_alloc_closure((void*)(l_Lake_inputTextFile___redArg___lam__0___boxed), 8, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lake_inputBinFile___redArg___closed__2;
x_11 = lean_box(1);
x_12 = lean_alloc_closure((void*)(l_Lake_inputBinFile___redArg___lam__1___boxed), 10, 9);
lean_closure_set(x_12, 0, x_8);
lean_closure_set(x_12, 1, x_11);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_3);
lean_closure_set(x_12, 4, x_4);
lean_closure_set(x_12, 5, x_5);
lean_closure_set(x_12, 6, x_6);
lean_closure_set(x_12, 7, x_10);
lean_closure_set(x_12, 8, x_9);
x_13 = lean_io_as_task(x_12, x_9, x_7);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lake_instDataKindFilePath;
x_17 = l_Lake_inputBinFile___redArg___closed__3;
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_17);
x_20 = lean_unbox(x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*3, x_20);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_23 = l_Lake_instDataKindFilePath;
x_24 = l_Lake_inputBinFile___redArg___closed__3;
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set(x_26, 2, x_24);
x_27 = lean_unbox(x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*3, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_22);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_inputTextFile___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_inputTextFile___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_inputTextFile(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (x_2 == 0)
{
lean_object* x_9; 
x_9 = l_Lake_inputBinFile___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = l_Lake_inputTextFile___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (x_2 == 0)
{
lean_object* x_10; 
x_10 = l_Lake_inputBinFile___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_9);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = l_Lake_inputTextFile___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lake_inputFile___redArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lake_inputFile(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_inputDir_spec__0(uint8_t x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_array_uget(x_4, x_3);
x_16 = lean_box(0);
x_17 = lean_array_uset(x_4, x_3, x_16);
if (x_1 == 0)
{
lean_object* x_26; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_26 = l_Lake_inputBinFile___redArg(x_15, x_5, x_6, x_7, x_8, x_9, x_11);
x_18 = x_26;
goto block_25;
}
else
{
lean_object* x_27; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_27 = l_Lake_inputTextFile___redArg(x_15, x_5, x_6, x_7, x_8, x_9, x_11);
x_18 = x_27;
goto block_25;
}
block_25:
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = lean_usize_add(x_3, x_21);
x_23 = lean_array_uset(x_17, x_3, x_19);
x_3 = x_22;
x_4 = x_23;
x_11 = x_20;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lake_inputDir_spec__1_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_array_uget(x_2, x_3);
x_13 = l_IO_FS_DirEntry_path(x_12);
lean_inc(x_1);
lean_inc(x_13);
x_14 = lean_apply_1(x_1, x_13);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_dec(x_13);
x_6 = x_5;
goto block_10;
}
else
{
lean_object* x_16; 
x_16 = lean_array_push(x_5, x_13);
x_6 = x_16;
goto block_10;
}
}
else
{
lean_dec(x_1);
return x_5;
}
block_10:
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
x_5 = x_6;
goto _start;
}
}
}
static lean_object* _init_l_Array_filterMapM___at___Lake_inputDir_spec__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lake_inputDir_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Array_filterMapM___at___Lake_inputDir_spec__1___closed__0;
x_6 = lean_nat_dec_lt(x_3, x_4);
if (x_6 == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_le(x_4, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_3);
x_10 = lean_usize_of_nat(x_4);
x_11 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lake_inputDir_spec__1_spec__1(x_1, x_2, x_9, x_10, x_5);
return x_11;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_qsort_sort___at___Lake_inputDir_spec__3___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_dec_lt(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lake_inputDir_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_alloc_closure((void*)(l_Array_qsort_sort___at___Lake_inputDir_spec__3___redArg___lam__0___boxed), 2, 0);
lean_inc(x_2);
x_6 = l_Array_qpartition___redArg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Array_qsort_sort___at___Lake_inputDir_spec__3___redArg(x_8, x_2, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lake_inputDir_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_qsort_sort___at___Lake_inputDir_spec__3___redArg(x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_18; 
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_9, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_9, 0);
lean_inc(x_39);
lean_dec(x_9);
x_40 = !lean_is_exclusive(x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_38, 1);
x_42 = l_Lake_BuildTrace_mix(x_1, x_41);
x_43 = lean_apply_1(x_2, x_39);
lean_ctor_set(x_38, 1, x_42);
x_44 = lean_box(1);
x_45 = lean_unbox(x_44);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_46 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_43, x_45, x_3, x_4, x_5, x_6, x_7, x_38, x_10);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_ctor_get(x_48, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_string_utf8_byte_size(x_51);
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_nat_dec_eq(x_53, x_54);
if (x_55 == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_50);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_57 = lean_ctor_get(x_50, 0);
x_58 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_59 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_51, x_53, x_54);
x_60 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_51, x_59, x_53);
x_61 = lean_string_utf8_extract(x_51, x_59, x_60);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_51);
x_62 = lean_string_append(x_58, x_61);
lean_dec(x_61);
x_63 = lean_box(1);
x_64 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_64, 0, x_62);
x_65 = lean_unbox(x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_65);
x_66 = lean_box(0);
x_67 = lean_array_push(x_57, x_64);
lean_ctor_set(x_50, 0, x_67);
x_68 = l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg___lam__1(x_52, x_66, x_3, x_4, x_5, x_6, x_7, x_50, x_49);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = x_68;
goto block_37;
}
else
{
lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_69 = lean_ctor_get(x_50, 0);
x_70 = lean_ctor_get_uint8(x_50, sizeof(void*)*2);
x_71 = lean_ctor_get(x_50, 1);
lean_inc(x_71);
lean_inc(x_69);
lean_dec(x_50);
x_72 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_73 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_51, x_53, x_54);
x_74 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_51, x_73, x_53);
x_75 = lean_string_utf8_extract(x_51, x_73, x_74);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_51);
x_76 = lean_string_append(x_72, x_75);
lean_dec(x_75);
x_77 = lean_box(1);
x_78 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_78, 0, x_76);
x_79 = lean_unbox(x_77);
lean_ctor_set_uint8(x_78, sizeof(void*)*1, x_79);
x_80 = lean_box(0);
x_81 = lean_array_push(x_69, x_78);
x_82 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_71);
lean_ctor_set_uint8(x_82, sizeof(void*)*2, x_70);
x_83 = l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg___lam__1(x_52, x_80, x_3, x_4, x_5, x_6, x_7, x_82, x_49);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = x_83;
goto block_37;
}
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_53);
lean_dec(x_51);
x_84 = lean_box(0);
x_85 = l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg___lam__1(x_52, x_84, x_3, x_4, x_5, x_6, x_7, x_50, x_49);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = x_85;
goto block_37;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_86 = lean_ctor_get(x_46, 1);
lean_inc(x_86);
lean_dec(x_46);
x_87 = lean_ctor_get(x_47, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_47, 1);
lean_inc(x_88);
lean_dec(x_47);
x_11 = x_87;
x_12 = x_88;
x_13 = x_86;
goto block_17;
}
}
else
{
lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; 
x_89 = lean_ctor_get(x_38, 0);
x_90 = lean_ctor_get_uint8(x_38, sizeof(void*)*2);
x_91 = lean_ctor_get(x_38, 1);
lean_inc(x_91);
lean_inc(x_89);
lean_dec(x_38);
x_92 = l_Lake_BuildTrace_mix(x_1, x_91);
x_93 = lean_apply_1(x_2, x_39);
x_94 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_94, 0, x_89);
lean_ctor_set(x_94, 1, x_92);
lean_ctor_set_uint8(x_94, sizeof(void*)*2, x_90);
x_95 = lean_box(1);
x_96 = lean_unbox(x_95);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_97 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_93, x_96, x_3, x_4, x_5, x_6, x_7, x_94, x_10);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_ctor_get(x_99, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
lean_dec(x_99);
x_104 = lean_string_utf8_byte_size(x_102);
x_105 = lean_unsigned_to_nat(0u);
x_106 = lean_nat_dec_eq(x_104, x_105);
if (x_106 == 0)
{
lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_107 = lean_ctor_get(x_101, 0);
lean_inc(x_107);
x_108 = lean_ctor_get_uint8(x_101, sizeof(void*)*2);
x_109 = lean_ctor_get(x_101, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_110 = x_101;
} else {
 lean_dec_ref(x_101);
 x_110 = lean_box(0);
}
x_111 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_112 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_102, x_104, x_105);
x_113 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_102, x_112, x_104);
x_114 = lean_string_utf8_extract(x_102, x_112, x_113);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_102);
x_115 = lean_string_append(x_111, x_114);
lean_dec(x_114);
x_116 = lean_box(1);
x_117 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_117, 0, x_115);
x_118 = lean_unbox(x_116);
lean_ctor_set_uint8(x_117, sizeof(void*)*1, x_118);
x_119 = lean_box(0);
x_120 = lean_array_push(x_107, x_117);
if (lean_is_scalar(x_110)) {
 x_121 = lean_alloc_ctor(0, 2, 1);
} else {
 x_121 = x_110;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_109);
lean_ctor_set_uint8(x_121, sizeof(void*)*2, x_108);
x_122 = l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg___lam__1(x_103, x_119, x_3, x_4, x_5, x_6, x_7, x_121, x_100);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = x_122;
goto block_37;
}
else
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_104);
lean_dec(x_102);
x_123 = lean_box(0);
x_124 = l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg___lam__1(x_103, x_123, x_3, x_4, x_5, x_6, x_7, x_101, x_100);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = x_124;
goto block_37;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_125 = lean_ctor_get(x_97, 1);
lean_inc(x_125);
lean_dec(x_97);
x_126 = lean_ctor_get(x_98, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_98, 1);
lean_inc(x_127);
lean_dec(x_98);
x_11 = x_126;
x_12 = x_127;
x_13 = x_125;
goto block_17;
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_9);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_task_pure(x_9);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_10);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_131 = lean_ctor_get(x_9, 0);
x_132 = lean_ctor_get(x_9, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_9);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_task_pure(x_133);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_10);
return x_135;
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
block_37:
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg___lam__0), 2, 1);
lean_closure_set(x_25, 0, x_23);
x_26 = lean_box(1);
x_27 = lean_unbox(x_26);
x_28 = lean_task_map(x_25, x_24, x_8, x_27);
lean_ctor_set(x_18, 0, x_28);
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_dec(x_18);
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_dec(x_19);
x_31 = lean_ctor_get(x_20, 0);
lean_inc(x_31);
lean_dec(x_20);
x_32 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg___lam__0), 2, 1);
lean_closure_set(x_32, 0, x_30);
x_33 = lean_box(1);
x_34 = lean_unbox(x_33);
x_35 = lean_task_map(x_32, x_31, x_8, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_29);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_15 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg___lam__2), 10, 8);
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
x_27 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg___lam__2), 10, 8);
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
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
x_13 = lean_io_read_dir(x_1, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_28; uint8_t x_29; 
lean_dec(x_12);
lean_dec(x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_16 = x_13;
} else {
 lean_dec_ref(x_13);
 x_16 = lean_box(0);
}
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_get_size(x_14);
x_23 = l_Array_filterMapM___at___Lake_inputDir_spec__1(x_2, x_14, x_21, x_22);
lean_dec(x_22);
lean_dec(x_14);
x_28 = lean_array_get_size(x_23);
x_29 = lean_nat_dec_eq(x_28, x_21);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_35; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_sub(x_28, x_30);
lean_dec(x_28);
x_35 = lean_nat_dec_le(x_21, x_31);
if (x_35 == 0)
{
lean_inc(x_31);
x_32 = x_31;
goto block_34;
}
else
{
x_32 = x_21;
goto block_34;
}
block_34:
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_32, x_31);
if (x_33 == 0)
{
lean_dec(x_31);
lean_inc(x_32);
x_24 = x_32;
x_25 = x_32;
goto block_27;
}
else
{
x_24 = x_32;
x_25 = x_31;
goto block_27;
}
}
}
else
{
lean_dec(x_28);
x_17 = x_23;
goto block_20;
}
block_20:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_8);
if (lean_is_scalar(x_16)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_16;
}
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
block_27:
{
lean_object* x_26; 
x_26 = l_Array_qsort_sort___at___Lake_inputDir_spec__3___redArg(x_23, x_24, x_25);
lean_dec(x_25);
x_17 = x_26;
goto block_20;
}
}
else
{
uint8_t x_36; 
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_8);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_8, 1);
lean_dec(x_37);
x_38 = lean_ctor_get(x_8, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_13);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_13, 0);
x_41 = lean_io_error_to_string(x_40);
x_42 = lean_box(3);
x_43 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_43, 0, x_41);
x_44 = lean_unbox(x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_44);
x_45 = lean_array_get_size(x_10);
x_46 = lean_array_push(x_10, x_43);
lean_ctor_set(x_8, 0, x_46);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_8);
lean_ctor_set_tag(x_13, 0);
lean_ctor_set(x_13, 0, x_47);
return x_13;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_48 = lean_ctor_get(x_13, 0);
x_49 = lean_ctor_get(x_13, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_13);
x_50 = lean_io_error_to_string(x_48);
x_51 = lean_box(3);
x_52 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_52, 0, x_50);
x_53 = lean_unbox(x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_53);
x_54 = lean_array_get_size(x_10);
x_55 = lean_array_push(x_10, x_52);
lean_ctor_set(x_8, 0, x_55);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_8);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_49);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_8);
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
x_61 = lean_io_error_to_string(x_58);
x_62 = lean_box(3);
x_63 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_63, 0, x_61);
x_64 = lean_unbox(x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_64);
x_65 = lean_array_get_size(x_10);
x_66 = lean_array_push(x_10, x_63);
x_67 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_12);
lean_ctor_set_uint8(x_67, sizeof(void*)*2, x_11);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_67);
if (lean_is_scalar(x_60)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_60;
 lean_ctor_set_tag(x_69, 0);
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_59);
return x_69;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10);
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
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_30 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_18, x_25, x_9);
x_31 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_18, x_30, x_25);
x_32 = lean_string_utf8_extract(x_18, x_30, x_31);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_18);
x_33 = lean_string_append(x_29, x_32);
lean_dec(x_32);
x_34 = lean_box(1);
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
x_36 = lean_unbox(x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_36);
x_37 = lean_array_push(x_28, x_35);
lean_ctor_set(x_16, 0, x_37);
x_20 = x_16;
x_21 = x_14;
goto block_24;
}
else
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_38 = lean_ctor_get(x_16, 0);
x_39 = lean_ctor_get_uint8(x_16, sizeof(void*)*2);
x_40 = lean_ctor_get(x_16, 1);
lean_inc(x_40);
lean_inc(x_38);
lean_dec(x_16);
x_41 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_42 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_18, x_25, x_9);
x_43 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_18, x_42, x_25);
x_44 = lean_string_utf8_extract(x_18, x_42, x_43);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_18);
x_45 = lean_string_append(x_41, x_44);
lean_dec(x_44);
x_46 = lean_box(1);
x_47 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_47, 0, x_45);
x_48 = lean_unbox(x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_48);
x_49 = lean_array_push(x_38, x_47);
x_50 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_40);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_39);
x_20 = x_50;
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
uint8_t x_51; 
lean_dec(x_9);
x_51 = !lean_is_exclusive(x_11);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_11, 0);
lean_dec(x_52);
x_53 = !lean_is_exclusive(x_12);
if (x_53 == 0)
{
return x_11;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_12, 0);
x_55 = lean_ctor_get(x_12, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_12);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_11, 0, x_56);
return x_11;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_11, 1);
lean_inc(x_57);
lean_dec(x_11);
x_58 = lean_ctor_get(x_12, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_12, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_60 = x_12;
} else {
 lean_dec_ref(x_12);
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
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_array_size(x_2);
x_11 = 0;
x_12 = l_Array_mapMUnsafe_map___at___Lake_inputDir_spec__0(x_1, x_10, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_Lake_buildFileAfterDepList___redArg___closed__0;
x_18 = l_Lake_Job_collectArray___redArg(x_16, x_17);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_18);
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = l_Lake_buildFileAfterDepList___redArg___closed__0;
x_22 = l_Lake_Job_collectArray___redArg(x_19, x_21);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_12, 0, x_23);
return x_12;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_12);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_28 = x_24;
} else {
 lean_dec_ref(x_24);
 x_28 = lean_box(0);
}
x_29 = l_Lake_buildFileAfterDepList___redArg___closed__0;
x_30 = l_Lake_Job_collectArray___redArg(x_26, x_29);
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
}
LEAN_EXPORT lean_object* l_Lake_inputDir(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; 
x_11 = lean_alloc_closure((void*)(l_Lake_inputDir___lam__0___boxed), 9, 2);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_3);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lake_inputBinFile___redArg___closed__2;
x_14 = lean_box(1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = lean_alloc_closure((void*)(l_Lake_inputDir___lam__1___boxed), 10, 9);
lean_closure_set(x_15, 0, x_11);
lean_closure_set(x_15, 1, x_14);
lean_closure_set(x_15, 2, x_4);
lean_closure_set(x_15, 3, x_5);
lean_closure_set(x_15, 4, x_6);
lean_closure_set(x_15, 5, x_7);
lean_closure_set(x_15, 6, x_8);
lean_closure_set(x_15, 7, x_13);
lean_closure_set(x_15, 8, x_12);
x_16 = lean_io_as_task(x_15, x_12, x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(x_2);
x_20 = lean_alloc_closure((void*)(l_Lake_inputDir___lam__2___boxed), 9, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_box(0);
x_22 = l_Lake_inputBinFile___redArg___closed__3;
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_22);
x_25 = lean_unbox(x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_25);
x_26 = lean_unbox(x_23);
x_27 = l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg(x_24, x_20, x_12, x_26, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
return x_27;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_inputDir_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_mapMUnsafe_map___at___Lake_inputDir_spec__0(x_12, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lake_inputDir_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lake_inputDir_spec__1_spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lake_inputDir_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_filterMapM___at___Lake_inputDir_spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lake_inputDir_spec__3___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_qsort_sort___at___Lake_inputDir_spec__3___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lake_inputDir_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsort_sort___at___Lake_inputDir_spec__3___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lake_inputDir_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_qsort_sort___at___Lake_inputDir_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Lake_Job_bindM___at___Lake_inputDir_spec__4(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_inputDir___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lake_inputDir___lam__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_Lake_inputDir___lam__2(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lake_inputDir(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT uint64_t l_Lake_buildO___lam__0(uint64_t x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; 
x_3 = 1723;
x_4 = lean_string_hash(x_2);
x_5 = lean_uint64_mix_hash(x_3, x_4);
x_6 = lean_uint64_mix_hash(x_1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = l_Lake_compileO(x_1, x_2, x_3, x_4, x_13, x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_15, 1);
lean_ctor_set(x_10, 0, x_19);
lean_ctor_set(x_15, 1, x_10);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
lean_ctor_set(x_10, 0, x_21);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_10);
lean_ctor_set(x_14, 0, x_22);
return x_14;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_dec(x_14);
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_26 = x_15;
} else {
 lean_dec_ref(x_15);
 x_26 = lean_box(0);
}
lean_ctor_set(x_10, 0, x_25);
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_26;
}
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_10);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_14);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_14, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_15);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_15, 1);
lean_ctor_set(x_10, 0, x_32);
lean_ctor_set(x_15, 1, x_10);
return x_14;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_15, 0);
x_34 = lean_ctor_get(x_15, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_15);
lean_ctor_set(x_10, 0, x_34);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_10);
lean_ctor_set(x_14, 0, x_35);
return x_14;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_14, 1);
lean_inc(x_36);
lean_dec(x_14);
x_37 = lean_ctor_get(x_15, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_15, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_39 = x_15;
} else {
 lean_dec_ref(x_15);
 x_39 = lean_box(0);
}
lean_ctor_set(x_10, 0, x_38);
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_10);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_36);
return x_41;
}
}
}
else
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_10, 0);
x_43 = lean_ctor_get_uint8(x_10, sizeof(void*)*2);
x_44 = lean_ctor_get(x_10, 1);
lean_inc(x_44);
lean_inc(x_42);
lean_dec(x_10);
x_45 = l_Lake_compileO(x_1, x_2, x_3, x_4, x_42, x_11);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_51 = x_46;
} else {
 lean_dec_ref(x_46);
 x_51 = lean_box(0);
}
x_52 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_44);
lean_ctor_set_uint8(x_52, sizeof(void*)*2, x_43);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set(x_53, 1, x_52);
if (lean_is_scalar(x_48)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_48;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_47);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_55 = lean_ctor_get(x_45, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_56 = x_45;
} else {
 lean_dec_ref(x_45);
 x_56 = lean_box(0);
}
x_57 = lean_ctor_get(x_46, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_46, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_59 = x_46;
} else {
 lean_dec_ref(x_46);
 x_59 = lean_box(0);
}
x_60 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_44);
lean_ctor_set_uint8(x_60, sizeof(void*)*2, x_43);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_57);
lean_ctor_set(x_61, 1, x_60);
if (lean_is_scalar(x_56)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_56;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_55);
return x_62;
}
}
}
}
static lean_object* _init_l_Lake_buildO___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("traceArgs: ", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_buildO___lam__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_buildO___lam__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("o", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_buildO___lam__2___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = 1723;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; uint64_t x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_20 = x_15;
} else {
 lean_dec_ref(x_15);
 x_20 = lean_box(0);
}
x_21 = l_Lake_platformTrace;
x_22 = l_Lake_BuildTrace_mix(x_19, x_21);
x_76 = 1723;
x_77 = lean_unsigned_to_nat(0u);
x_78 = lean_array_get_size(x_1);
x_79 = lean_nat_dec_lt(x_77, x_78);
if (x_79 == 0)
{
lean_dec(x_78);
lean_dec(x_8);
lean_dec(x_7);
x_23 = x_76;
goto block_75;
}
else
{
uint8_t x_80; 
x_80 = lean_nat_dec_le(x_78, x_78);
if (x_80 == 0)
{
lean_dec(x_78);
lean_dec(x_8);
lean_dec(x_7);
x_23 = x_76;
goto block_75;
}
else
{
size_t x_81; size_t x_82; lean_object* x_83; lean_object* x_84; uint64_t x_85; 
x_81 = 0;
x_82 = lean_usize_of_nat(x_78);
lean_dec(x_78);
x_83 = l_Lake_buildO___lam__2___boxed__const__1;
lean_inc(x_1);
x_84 = l_Array_foldlMUnsafe_fold___redArg(x_7, x_8, x_1, x_81, x_82, x_83);
x_85 = lean_unbox_uint64(x_84);
lean_dec(x_84);
x_23 = x_85;
goto block_75;
}
}
block_75:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_24 = l_Lake_buildO___lam__2___closed__0;
x_25 = l_Lake_buildO___lam__2___closed__1;
lean_inc(x_1);
x_26 = lean_array_to_list(x_1);
x_27 = l_List_toString___redArg(x_2, x_26);
x_28 = lean_string_append(x_25, x_27);
lean_dec(x_27);
x_29 = lean_string_append(x_24, x_28);
lean_dec(x_28);
x_30 = l_Lake_platformTrace___closed__2;
x_31 = l_Lake_platformTrace___closed__4;
x_32 = lean_box_uint64(x_23);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_30);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set(x_33, 3, x_31);
x_34 = l_Lake_BuildTrace_mix(x_22, x_33);
if (lean_is_scalar(x_20)) {
 x_35 = lean_alloc_ctor(0, 2, 1);
} else {
 x_35 = x_20;
}
lean_ctor_set(x_35, 0, x_17);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_18);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_36 = lean_apply_7(x_3, x_10, x_11, x_12, x_13, x_14, x_35, x_16);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_ctor_get(x_37, 0);
lean_inc(x_40);
lean_dec(x_37);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; lean_object* x_50; 
x_42 = lean_ctor_get(x_38, 1);
x_43 = l_Lake_BuildTrace_mix(x_42, x_40);
lean_ctor_set(x_38, 1, x_43);
x_44 = l_Array_append___redArg(x_4, x_1);
lean_dec(x_1);
lean_inc(x_5);
x_45 = lean_alloc_closure((void*)(l_Lake_buildO___lam__1___boxed), 11, 4);
lean_closure_set(x_45, 0, x_5);
lean_closure_set(x_45, 1, x_9);
lean_closure_set(x_45, 2, x_44);
lean_closure_set(x_45, 3, x_6);
x_46 = lean_box(0);
x_47 = l_Lake_buildO___lam__2___closed__2;
x_48 = lean_unbox(x_46);
x_49 = lean_unbox(x_46);
x_50 = l_Lake_buildArtifactUnlessUpToDate(x_5, x_45, x_48, x_47, x_49, x_10, x_11, x_12, x_13, x_14, x_38, x_39);
return x_50;
}
else
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_61; lean_object* x_62; 
x_51 = lean_ctor_get(x_38, 0);
x_52 = lean_ctor_get_uint8(x_38, sizeof(void*)*2);
x_53 = lean_ctor_get(x_38, 1);
lean_inc(x_53);
lean_inc(x_51);
lean_dec(x_38);
x_54 = l_Lake_BuildTrace_mix(x_53, x_40);
x_55 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*2, x_52);
x_56 = l_Array_append___redArg(x_4, x_1);
lean_dec(x_1);
lean_inc(x_5);
x_57 = lean_alloc_closure((void*)(l_Lake_buildO___lam__1___boxed), 11, 4);
lean_closure_set(x_57, 0, x_5);
lean_closure_set(x_57, 1, x_9);
lean_closure_set(x_57, 2, x_56);
lean_closure_set(x_57, 3, x_6);
x_58 = lean_box(0);
x_59 = l_Lake_buildO___lam__2___closed__2;
x_60 = lean_unbox(x_58);
x_61 = lean_unbox(x_58);
x_62 = l_Lake_buildArtifactUnlessUpToDate(x_5, x_57, x_60, x_59, x_61, x_10, x_11, x_12, x_13, x_14, x_55, x_39);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_36);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_36, 0);
lean_dec(x_64);
x_65 = !lean_is_exclusive(x_37);
if (x_65 == 0)
{
return x_36;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_37, 0);
x_67 = lean_ctor_get(x_37, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_37);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_36, 0, x_68);
return x_36;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_36, 1);
lean_inc(x_69);
lean_dec(x_36);
x_70 = lean_ctor_get(x_37, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_37, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_72 = x_37;
} else {
 lean_dec_ref(x_37);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_69);
return x_74;
}
}
}
}
}
static lean_object* _init_l_Lake_buildO___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instToStringString___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_14 = lean_alloc_closure((void*)(l_Lake_buildO___lam__0___boxed), 2, 0);
x_15 = l_Lake_instDataKindFilePath;
x_16 = l_Lake_buildO___closed__0;
x_17 = l_Lake_instMonadWorkspaceJobM___closed__10;
x_18 = lean_alloc_closure((void*)(l_Lake_buildO___lam__2), 16, 8);
lean_closure_set(x_18, 0, x_4);
lean_closure_set(x_18, 1, x_16);
lean_closure_set(x_18, 2, x_6);
lean_closure_set(x_18, 3, x_3);
lean_closure_set(x_18, 4, x_1);
lean_closure_set(x_18, 5, x_5);
lean_closure_set(x_18, 6, x_17);
lean_closure_set(x_18, 7, x_14);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_box(0);
x_21 = lean_unbox(x_20);
x_22 = l_Lake_Job_mapM___redArg(x_15, x_2, x_18, x_19, x_21, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Lake_buildO___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_buildO___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT uint64_t l_Array_foldlMUnsafe_fold___at___Lake_buildLeanO_spec__0(lean_object* x_1, size_t x_2, size_t x_3, uint64_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; size_t x_11; size_t x_12; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1723;
x_8 = lean_string_hash(x_6);
lean_dec(x_6);
x_9 = lean_uint64_mix_hash(x_7, x_8);
x_10 = lean_uint64_mix_hash(x_4, x_9);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_10;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildLeanO_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_10, 1);
x_14 = l_Lake_BuildTrace_mix(x_1, x_13);
x_15 = lean_apply_1(x_2, x_11);
lean_ctor_set(x_10, 1, x_14);
x_16 = lean_box(1);
x_17 = lean_unbox(x_16);
x_18 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_15, x_17, x_3, x_4, x_5, x_6, x_7, x_10, x_9);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_22 = x_18;
} else {
 lean_dec_ref(x_18);
 x_22 = lean_box(0);
}
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_24 = x_19;
} else {
 lean_dec_ref(x_19);
 x_24 = lean_box(0);
}
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_dec(x_20);
x_32 = lean_string_utf8_byte_size(x_25);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_nat_dec_eq(x_32, x_33);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_23);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_36 = lean_ctor_get(x_23, 0);
x_37 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_38 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_25, x_32, x_33);
x_39 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_25, x_38, x_32);
x_40 = lean_string_utf8_extract(x_25, x_38, x_39);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_25);
x_41 = lean_string_append(x_37, x_40);
lean_dec(x_40);
x_42 = lean_box(1);
x_43 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_43, 0, x_41);
x_44 = lean_unbox(x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_44);
x_45 = lean_array_push(x_36, x_43);
lean_ctor_set(x_23, 0, x_45);
x_27 = x_23;
x_28 = x_21;
goto block_31;
}
else
{
lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_46 = lean_ctor_get(x_23, 0);
x_47 = lean_ctor_get_uint8(x_23, sizeof(void*)*2);
x_48 = lean_ctor_get(x_23, 1);
lean_inc(x_48);
lean_inc(x_46);
lean_dec(x_23);
x_49 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_50 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_25, x_32, x_33);
x_51 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_25, x_50, x_32);
x_52 = lean_string_utf8_extract(x_25, x_50, x_51);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_25);
x_53 = lean_string_append(x_49, x_52);
lean_dec(x_52);
x_54 = lean_box(1);
x_55 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_55, 0, x_53);
x_56 = lean_unbox(x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_56);
x_57 = lean_array_push(x_46, x_55);
x_58 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_48);
lean_ctor_set_uint8(x_58, sizeof(void*)*2, x_47);
x_27 = x_58;
x_28 = x_21;
goto block_31;
}
}
else
{
lean_dec(x_32);
lean_dec(x_25);
x_27 = x_23;
x_28 = x_21;
goto block_31;
}
block_31:
{
lean_object* x_29; lean_object* x_30; 
if (lean_is_scalar(x_24)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_24;
}
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_27);
if (lean_is_scalar(x_22)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_22;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_18);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_18, 0);
lean_dec(x_60);
x_61 = !lean_is_exclusive(x_19);
if (x_61 == 0)
{
return x_18;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_19, 0);
x_63 = lean_ctor_get(x_19, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_19);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_18, 0, x_64);
return x_18;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_18, 1);
lean_inc(x_65);
lean_dec(x_18);
x_66 = lean_ctor_get(x_19, 0);
lean_inc(x_66);
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
return x_70;
}
}
}
else
{
lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; 
x_71 = lean_ctor_get(x_10, 0);
x_72 = lean_ctor_get_uint8(x_10, sizeof(void*)*2);
x_73 = lean_ctor_get(x_10, 1);
lean_inc(x_73);
lean_inc(x_71);
lean_dec(x_10);
x_74 = l_Lake_BuildTrace_mix(x_1, x_73);
x_75 = lean_apply_1(x_2, x_11);
x_76 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_76, 0, x_71);
lean_ctor_set(x_76, 1, x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*2, x_72);
x_77 = lean_box(1);
x_78 = lean_unbox(x_77);
x_79 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_75, x_78, x_3, x_4, x_5, x_6, x_7, x_76, x_9);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_83 = x_79;
} else {
 lean_dec_ref(x_79);
 x_83 = lean_box(0);
}
x_84 = lean_ctor_get(x_80, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_85 = x_80;
} else {
 lean_dec_ref(x_80);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get(x_81, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_81, 1);
lean_inc(x_87);
lean_dec(x_81);
x_93 = lean_string_utf8_byte_size(x_86);
x_94 = lean_unsigned_to_nat(0u);
x_95 = lean_nat_dec_eq(x_93, x_94);
if (x_95 == 0)
{
lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; 
x_96 = lean_ctor_get(x_84, 0);
lean_inc(x_96);
x_97 = lean_ctor_get_uint8(x_84, sizeof(void*)*2);
x_98 = lean_ctor_get(x_84, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_99 = x_84;
} else {
 lean_dec_ref(x_84);
 x_99 = lean_box(0);
}
x_100 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_101 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_86, x_93, x_94);
x_102 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_86, x_101, x_93);
x_103 = lean_string_utf8_extract(x_86, x_101, x_102);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_86);
x_104 = lean_string_append(x_100, x_103);
lean_dec(x_103);
x_105 = lean_box(1);
x_106 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_106, 0, x_104);
x_107 = lean_unbox(x_105);
lean_ctor_set_uint8(x_106, sizeof(void*)*1, x_107);
x_108 = lean_array_push(x_96, x_106);
if (lean_is_scalar(x_99)) {
 x_109 = lean_alloc_ctor(0, 2, 1);
} else {
 x_109 = x_99;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_98);
lean_ctor_set_uint8(x_109, sizeof(void*)*2, x_97);
x_88 = x_109;
x_89 = x_82;
goto block_92;
}
else
{
lean_dec(x_93);
lean_dec(x_86);
x_88 = x_84;
x_89 = x_82;
goto block_92;
}
block_92:
{
lean_object* x_90; lean_object* x_91; 
if (lean_is_scalar(x_85)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_85;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
if (lean_is_scalar(x_83)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_83;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_110 = lean_ctor_get(x_79, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_111 = x_79;
} else {
 lean_dec_ref(x_79);
 x_111 = lean_box(0);
}
x_112 = lean_ctor_get(x_80, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_80, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_114 = x_80;
} else {
 lean_dec_ref(x_80);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
if (lean_is_scalar(x_111)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_111;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_110);
return x_116;
}
}
}
else
{
uint8_t x_117; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_117 = !lean_is_exclusive(x_8);
if (x_117 == 0)
{
lean_object* x_118; 
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_8);
lean_ctor_set(x_118, 1, x_9);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = lean_ctor_get(x_8, 0);
x_120 = lean_ctor_get(x_8, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_8);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_9);
return x_122;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildLeanO_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_15 = lean_alloc_closure((void*)(l_Lake_Job_mapM___at___Lake_buildLeanO_spec__1___redArg___lam__0), 9, 7);
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
x_19 = l_Lake_instDataKindFilePath;
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
x_22 = l_Lake_instDataKindFilePath;
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
x_27 = lean_alloc_closure((void*)(l_Lake_Job_mapM___at___Lake_buildLeanO_spec__1___redArg___lam__0), 9, 7);
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
x_32 = l_Lake_instDataKindFilePath;
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
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildLeanO_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_Job_mapM___at___Lake_buildLeanO_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
static lean_object* _init_l_Lake_buildLeanO___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-I", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_buildLeanO___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_buildLeanO___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_buildLeanO___lam__0___closed__0;
x_2 = l_Lake_buildLeanO___lam__0___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_11, sizeof(void*)*2);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_18 = x_11;
} else {
 lean_dec_ref(x_11);
 x_18 = lean_box(0);
}
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_19, 4);
lean_inc(x_63);
x_20 = x_63;
goto block_62;
}
else
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_5, 0);
lean_inc(x_64);
lean_dec(x_5);
x_20 = x_64;
goto block_62;
}
block_62:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_19, 12);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 16);
lean_inc(x_22);
lean_dec(x_19);
x_23 = l_Lake_buildLeanO___lam__0___closed__2;
x_24 = lean_array_push(x_23, x_20);
x_25 = l_Array_append___redArg(x_24, x_22);
lean_dec(x_22);
x_26 = l_Array_append___redArg(x_25, x_1);
x_27 = l_Array_append___redArg(x_26, x_2);
x_28 = l_Lake_compileO(x_3, x_4, x_27, x_21, x_15, x_12);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_28, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_29, 1);
if (lean_is_scalar(x_18)) {
 x_34 = lean_alloc_ctor(0, 2, 1);
} else {
 x_34 = x_18;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_17);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_16);
lean_ctor_set(x_29, 1, x_34);
return x_28;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
if (lean_is_scalar(x_18)) {
 x_37 = lean_alloc_ctor(0, 2, 1);
} else {
 x_37 = x_18;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_17);
lean_ctor_set_uint8(x_37, sizeof(void*)*2, x_16);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_28, 0, x_38);
return x_28;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_28, 1);
lean_inc(x_39);
lean_dec(x_28);
x_40 = lean_ctor_get(x_29, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_29, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_42 = x_29;
} else {
 lean_dec_ref(x_29);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_18)) {
 x_43 = lean_alloc_ctor(0, 2, 1);
} else {
 x_43 = x_18;
}
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_17);
lean_ctor_set_uint8(x_43, sizeof(void*)*2, x_16);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_39);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_28);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_28, 0);
lean_dec(x_47);
x_48 = !lean_is_exclusive(x_29);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_29, 1);
if (lean_is_scalar(x_18)) {
 x_50 = lean_alloc_ctor(0, 2, 1);
} else {
 x_50 = x_18;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_17);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_16);
lean_ctor_set(x_29, 1, x_50);
return x_28;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_29, 0);
x_52 = lean_ctor_get(x_29, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_29);
if (lean_is_scalar(x_18)) {
 x_53 = lean_alloc_ctor(0, 2, 1);
} else {
 x_53 = x_18;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_17);
lean_ctor_set_uint8(x_53, sizeof(void*)*2, x_16);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_28, 0, x_54);
return x_28;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_28, 1);
lean_inc(x_55);
lean_dec(x_28);
x_56 = lean_ctor_get(x_29, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_29, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_58 = x_29;
} else {
 lean_dec_ref(x_29);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_18)) {
 x_59 = lean_alloc_ctor(0, 2, 1);
} else {
 x_59 = x_18;
}
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_17);
lean_ctor_set_uint8(x_59, sizeof(void*)*2, x_16);
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_56);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_55);
return x_61;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint64_t x_20; uint64_t x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_11, sizeof(void*)*2);
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
x_17 = lean_ctor_get(x_10, 2);
lean_inc(x_17);
lean_inc(x_3);
lean_inc(x_2);
x_18 = lean_alloc_closure((void*)(l_Lake_buildLeanO___lam__0___boxed), 12, 5);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_3);
lean_closure_set(x_18, 3, x_5);
lean_closure_set(x_18, 4, x_4);
x_19 = l_Lake_BuildTrace_mix(x_15, x_17);
x_41 = 1723;
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_array_get_size(x_2);
x_44 = lean_nat_dec_lt(x_42, x_43);
if (x_44 == 0)
{
lean_dec(x_43);
x_20 = x_41;
goto block_40;
}
else
{
uint8_t x_45; 
x_45 = lean_nat_dec_le(x_43, x_43);
if (x_45 == 0)
{
lean_dec(x_43);
x_20 = x_41;
goto block_40;
}
else
{
size_t x_46; size_t x_47; uint64_t x_48; 
x_46 = 0;
x_47 = lean_usize_of_nat(x_43);
lean_dec(x_43);
x_48 = l_Array_foldlMUnsafe_fold___at___Lake_buildLeanO_spec__0(x_2, x_46, x_47, x_41);
x_20 = x_48;
goto block_40;
}
}
block_40:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; 
x_21 = l_Lake_buildO___lam__2___closed__0;
x_22 = l_Lake_buildO___lam__2___closed__1;
x_23 = lean_array_to_list(x_2);
x_24 = l_List_toString___at___Lean_rewriteManualLinksCore_rw_spec__0(x_23);
lean_dec(x_23);
x_25 = lean_string_append(x_22, x_24);
lean_dec(x_24);
x_26 = lean_string_append(x_21, x_25);
lean_dec(x_25);
x_27 = l_Lake_platformTrace___closed__2;
x_28 = l_Lake_platformTrace___closed__4;
x_29 = lean_box_uint64(x_20);
x_30 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_27);
lean_ctor_set(x_30, 2, x_29);
lean_ctor_set(x_30, 3, x_28);
x_31 = l_Lake_BuildTrace_mix(x_19, x_30);
x_32 = l_Lake_platformTrace;
x_33 = l_Lake_BuildTrace_mix(x_31, x_32);
if (lean_is_scalar(x_16)) {
 x_34 = lean_alloc_ctor(0, 2, 1);
} else {
 x_34 = x_16;
}
lean_ctor_set(x_34, 0, x_13);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_14);
x_35 = lean_box(0);
x_36 = l_Lake_buildO___lam__2___closed__2;
x_37 = lean_unbox(x_35);
x_38 = lean_unbox(x_35);
x_39 = l_Lake_buildArtifactUnlessUpToDate(x_3, x_18, x_37, x_36, x_38, x_6, x_7, x_8, x_9, x_10, x_34, x_12);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_13 = lean_alloc_closure((void*)(l_Lake_buildLeanO___lam__1), 12, 4);
lean_closure_set(x_13, 0, x_3);
lean_closure_set(x_13, 1, x_4);
lean_closure_set(x_13, 2, x_1);
lean_closure_set(x_13, 3, x_5);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_box(0);
x_16 = lean_unbox(x_15);
x_17 = l_Lake_Job_mapM___at___Lake_buildLeanO_spec__1___redArg(x_2, x_13, x_14, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_buildLeanO_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Lake_buildLeanO_spec__0(x_1, x_5, x_6, x_7);
lean_dec(x_1);
x_9 = lean_box_uint64(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildLeanO_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lake_Job_mapM___at___Lake_buildLeanO_spec__1___redArg(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildLeanO_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Lake_Job_mapM___at___Lake_buildLeanO_spec__1(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_buildLeanO___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_13, 11);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lake_compileStaticLib(x_1, x_2, x_16, x_3, x_15, x_10);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_18, 1);
lean_ctor_set(x_9, 0, x_22);
lean_ctor_set(x_18, 1, x_9);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
lean_ctor_set(x_9, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_9);
lean_ctor_set(x_17, 0, x_25);
return x_17;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_29 = x_18;
} else {
 lean_dec_ref(x_18);
 x_29 = lean_box(0);
}
lean_ctor_set(x_9, 0, x_28);
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_9);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_17, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_18);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_18, 1);
lean_ctor_set(x_9, 0, x_35);
lean_ctor_set(x_18, 1, x_9);
return x_17;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_18, 0);
x_37 = lean_ctor_get(x_18, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_18);
lean_ctor_set(x_9, 0, x_37);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_9);
lean_ctor_set(x_17, 0, x_38);
return x_17;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_17, 1);
lean_inc(x_39);
lean_dec(x_17);
x_40 = lean_ctor_get(x_18, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_42 = x_18;
} else {
 lean_dec_ref(x_18);
 x_42 = lean_box(0);
}
lean_ctor_set(x_9, 0, x_41);
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_9);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_39);
return x_44;
}
}
}
else
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_9, 0);
x_46 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
x_47 = lean_ctor_get(x_9, 1);
lean_inc(x_47);
lean_inc(x_45);
lean_dec(x_9);
x_48 = lean_ctor_get(x_13, 11);
lean_inc(x_48);
lean_dec(x_13);
x_49 = l_Lake_compileStaticLib(x_1, x_2, x_48, x_3, x_45, x_10);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
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
x_53 = lean_ctor_get(x_50, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_55 = x_50;
} else {
 lean_dec_ref(x_50);
 x_55 = lean_box(0);
}
x_56 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_47);
lean_ctor_set_uint8(x_56, sizeof(void*)*2, x_46);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_56);
if (lean_is_scalar(x_52)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_52;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_51);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_59 = lean_ctor_get(x_49, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_60 = x_49;
} else {
 lean_dec_ref(x_49);
 x_60 = lean_box(0);
}
x_61 = lean_ctor_get(x_50, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_50, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_63 = x_50;
} else {
 lean_dec_ref(x_50);
 x_63 = lean_box(0);
}
x_64 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_47);
lean_ctor_set_uint8(x_64, sizeof(void*)*2, x_46);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_61);
lean_ctor_set(x_65, 1, x_64);
if (lean_is_scalar(x_60)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_60;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_59);
return x_66;
}
}
}
}
static lean_object* _init_l_Lake_buildStaticLib___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("a", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_11 = lean_box(x_2);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lam__0___boxed), 10, 3);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_11);
x_13 = lean_box(0);
x_14 = l_Lake_buildStaticLib___lam__1___closed__0;
x_15 = lean_unbox(x_13);
x_16 = lean_unbox(x_13);
x_17 = l_Lake_buildArtifactUnlessUpToDate(x_1, x_12, x_15, x_14, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_17;
}
}
static lean_object* _init_l_Lake_buildStaticLib___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("objs", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_11 = lean_box(x_3);
x_12 = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lam__1___boxed), 10, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
x_13 = l_Lake_buildStaticLib___closed__0;
x_14 = l_Lake_Job_collectArray___redArg(x_2, x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
x_18 = l_Lake_Job_mapM___at___Lake_buildLeanO_spec__1___redArg(x_14, x_12, x_15, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lake_buildStaticLib___lam__0(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lake_buildStaticLib___lam__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lake_buildStaticLib(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_3);
x_7 = lean_array_push(x_4, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
x_4 = x_7;
goto _start;
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-l", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-L", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_16; 
x_6 = lean_array_uget(x_1, x_3);
x_16 = l_Lake_Dynlib_dir_x3f(x_6);
if (lean_obj_tag(x_16) == 0)
{
x_7 = x_4;
goto block_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = lean_array_push(x_4, x_19);
x_7 = x_20;
goto block_15;
}
block_15:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_array_push(x_7, x_10);
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_3 = x_13;
x_4 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; size_t x_7; lean_object* x_8; 
x_3 = l_Array_filterMapM___at___Lake_inputDir_spec__1___closed__0;
x_4 = lean_array_size(x_1);
x_5 = 0;
x_6 = l_Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(x_1, x_4, x_5, x_3);
x_7 = lean_array_size(x_2);
x_8 = l_Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(x_2, x_7, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_10 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(x_9, x_1, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_1);
return x_10;
}
else
{
lean_object* x_11; size_t x_12; size_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_3 = x_13;
x_5 = x_11;
goto _start;
}
}
else
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_5);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_array_push(x_4, x_1);
x_8 = l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(x_3, x_5);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = l_List_elem___at___Lake_envToBool_x3f_spec__1(x_5, x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_box(0);
lean_inc(x_5);
x_11 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_3, x_5, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_get_size(x_6);
x_15 = lean_nat_dec_lt(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_14, x_14);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_12);
return x_18;
}
else
{
lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_2);
x_20 = 0;
x_21 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_22 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(x_19, x_6, x_20, x_21, x_12);
lean_dec(x_6);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_2);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_8);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_8, 0);
lean_dec(x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_7);
lean_ctor_set(x_8, 0, x_27);
return x_8;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_8);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_3);
lean_ctor_set(x_28, 1, x_7);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_2);
x_9 = lean_box(0);
x_10 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(x_8, x_9, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
return x_10;
}
else
{
lean_object* x_11; size_t x_12; size_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_11;
goto _start;
}
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
}
}
static lean_object* _init_l_List_mapTR_loop___at___Lake_formatCycle___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lake_formatCycle___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_List_mapTR_loop___at___Lake_formatCycle___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1_spec__1___closed__0;
x_8 = lean_string_append(x_7, x_5);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_8);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = l_List_mapTR_loop___at___Lake_formatCycle___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1_spec__1___closed__0;
x_13 = lean_string_append(x_12, x_10);
lean_dec(x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
x_1 = x_11;
x_2 = x_14;
goto _start;
}
}
}
}
static lean_object* _init_l_Lake_formatCycle___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_formatCycle___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lake_formatCycle___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1___closed__0;
x_3 = lean_box(0);
x_4 = l_List_mapTR_loop___at___Lake_formatCycle___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1_spec__1(x_1, x_3);
x_5 = l_String_intercalate(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("library dependency cycle:\n", 26, 26);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0;
x_10 = lean_array_get_size(x_1);
x_11 = lean_nat_dec_lt(x_8, x_10);
if (x_11 == 0)
{
lean_dec(x_10);
x_4 = x_9;
goto block_7;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_10, x_10);
if (x_12 == 0)
{
lean_dec(x_10);
x_4 = x_9;
goto block_7;
}
else
{
lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1;
x_14 = 0;
x_15 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_16 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0(x_1, x_14, x_15, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2;
x_21 = l_Lake_formatCycle___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(x_17);
x_22 = lean_string_append(x_20, x_21);
lean_dec(x_21);
x_23 = lean_box(3);
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_22);
x_25 = lean_unbox(x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_25);
x_26 = lean_array_get_size(x_19);
x_27 = lean_array_push(x_19, x_24);
lean_ctor_set(x_2, 0, x_27);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_2);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_3);
return x_29;
}
else
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_30 = lean_ctor_get(x_2, 0);
x_31 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_32 = lean_ctor_get(x_2, 1);
lean_inc(x_32);
lean_inc(x_30);
lean_dec(x_2);
x_33 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2;
x_34 = l_Lake_formatCycle___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(x_17);
x_35 = lean_string_append(x_33, x_34);
lean_dec(x_34);
x_36 = lean_box(3);
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_35);
x_38 = lean_unbox(x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_38);
x_39 = lean_array_get_size(x_30);
x_40 = lean_array_push(x_30, x_37);
x_41 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_32);
lean_ctor_set_uint8(x_41, sizeof(void*)*2, x_31);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_3);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_16, 0);
lean_inc(x_44);
lean_dec(x_16);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_4 = x_45;
goto block_7;
}
}
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(x_1, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_10, 1);
x_14 = l_Lake_BuildTrace_mix(x_1, x_13);
x_15 = lean_apply_1(x_2, x_11);
lean_ctor_set(x_10, 1, x_14);
x_16 = lean_box(1);
x_17 = lean_unbox(x_16);
x_18 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_15, x_17, x_3, x_4, x_5, x_6, x_7, x_10, x_9);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_22 = x_18;
} else {
 lean_dec_ref(x_18);
 x_22 = lean_box(0);
}
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_24 = x_19;
} else {
 lean_dec_ref(x_19);
 x_24 = lean_box(0);
}
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_dec(x_20);
x_32 = lean_string_utf8_byte_size(x_25);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_nat_dec_eq(x_32, x_33);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_23);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_36 = lean_ctor_get(x_23, 0);
x_37 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_38 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_25, x_32, x_33);
x_39 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_25, x_38, x_32);
x_40 = lean_string_utf8_extract(x_25, x_38, x_39);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_25);
x_41 = lean_string_append(x_37, x_40);
lean_dec(x_40);
x_42 = lean_box(1);
x_43 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_43, 0, x_41);
x_44 = lean_unbox(x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_44);
x_45 = lean_array_push(x_36, x_43);
lean_ctor_set(x_23, 0, x_45);
x_27 = x_23;
x_28 = x_21;
goto block_31;
}
else
{
lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_46 = lean_ctor_get(x_23, 0);
x_47 = lean_ctor_get_uint8(x_23, sizeof(void*)*2);
x_48 = lean_ctor_get(x_23, 1);
lean_inc(x_48);
lean_inc(x_46);
lean_dec(x_23);
x_49 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_50 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_25, x_32, x_33);
x_51 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_25, x_50, x_32);
x_52 = lean_string_utf8_extract(x_25, x_50, x_51);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_25);
x_53 = lean_string_append(x_49, x_52);
lean_dec(x_52);
x_54 = lean_box(1);
x_55 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_55, 0, x_53);
x_56 = lean_unbox(x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_56);
x_57 = lean_array_push(x_46, x_55);
x_58 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_48);
lean_ctor_set_uint8(x_58, sizeof(void*)*2, x_47);
x_27 = x_58;
x_28 = x_21;
goto block_31;
}
}
else
{
lean_dec(x_32);
lean_dec(x_25);
x_27 = x_23;
x_28 = x_21;
goto block_31;
}
block_31:
{
lean_object* x_29; lean_object* x_30; 
if (lean_is_scalar(x_24)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_24;
}
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_27);
if (lean_is_scalar(x_22)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_22;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_18);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_18, 0);
lean_dec(x_60);
x_61 = !lean_is_exclusive(x_19);
if (x_61 == 0)
{
return x_18;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_19, 0);
x_63 = lean_ctor_get(x_19, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_19);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_18, 0, x_64);
return x_18;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_18, 1);
lean_inc(x_65);
lean_dec(x_18);
x_66 = lean_ctor_get(x_19, 0);
lean_inc(x_66);
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
return x_70;
}
}
}
else
{
lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; 
x_71 = lean_ctor_get(x_10, 0);
x_72 = lean_ctor_get_uint8(x_10, sizeof(void*)*2);
x_73 = lean_ctor_get(x_10, 1);
lean_inc(x_73);
lean_inc(x_71);
lean_dec(x_10);
x_74 = l_Lake_BuildTrace_mix(x_1, x_73);
x_75 = lean_apply_1(x_2, x_11);
x_76 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_76, 0, x_71);
lean_ctor_set(x_76, 1, x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*2, x_72);
x_77 = lean_box(1);
x_78 = lean_unbox(x_77);
x_79 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_75, x_78, x_3, x_4, x_5, x_6, x_7, x_76, x_9);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_83 = x_79;
} else {
 lean_dec_ref(x_79);
 x_83 = lean_box(0);
}
x_84 = lean_ctor_get(x_80, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_85 = x_80;
} else {
 lean_dec_ref(x_80);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get(x_81, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_81, 1);
lean_inc(x_87);
lean_dec(x_81);
x_93 = lean_string_utf8_byte_size(x_86);
x_94 = lean_unsigned_to_nat(0u);
x_95 = lean_nat_dec_eq(x_93, x_94);
if (x_95 == 0)
{
lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; 
x_96 = lean_ctor_get(x_84, 0);
lean_inc(x_96);
x_97 = lean_ctor_get_uint8(x_84, sizeof(void*)*2);
x_98 = lean_ctor_get(x_84, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_99 = x_84;
} else {
 lean_dec_ref(x_84);
 x_99 = lean_box(0);
}
x_100 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_101 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_86, x_93, x_94);
x_102 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_86, x_101, x_93);
x_103 = lean_string_utf8_extract(x_86, x_101, x_102);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_86);
x_104 = lean_string_append(x_100, x_103);
lean_dec(x_103);
x_105 = lean_box(1);
x_106 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_106, 0, x_104);
x_107 = lean_unbox(x_105);
lean_ctor_set_uint8(x_106, sizeof(void*)*1, x_107);
x_108 = lean_array_push(x_96, x_106);
if (lean_is_scalar(x_99)) {
 x_109 = lean_alloc_ctor(0, 2, 1);
} else {
 x_109 = x_99;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_98);
lean_ctor_set_uint8(x_109, sizeof(void*)*2, x_97);
x_88 = x_109;
x_89 = x_82;
goto block_92;
}
else
{
lean_dec(x_93);
lean_dec(x_86);
x_88 = x_84;
x_89 = x_82;
goto block_92;
}
block_92:
{
lean_object* x_90; lean_object* x_91; 
if (lean_is_scalar(x_85)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_85;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
if (lean_is_scalar(x_83)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_83;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_110 = lean_ctor_get(x_79, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_111 = x_79;
} else {
 lean_dec_ref(x_79);
 x_111 = lean_box(0);
}
x_112 = lean_ctor_get(x_80, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_80, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_114 = x_80;
} else {
 lean_dec_ref(x_80);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
if (lean_is_scalar(x_111)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_111;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_110);
return x_116;
}
}
}
else
{
uint8_t x_117; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_117 = !lean_is_exclusive(x_8);
if (x_117 == 0)
{
lean_object* x_118; 
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_8);
lean_ctor_set(x_118, 1, x_9);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = lean_ctor_get(x_8, 0);
x_120 = lean_ctor_get(x_8, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_8);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_9);
return x_122;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_15 = lean_alloc_closure((void*)(l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___redArg___lam__0), 9, 7);
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
x_19 = l_Lake_instDataKindDynlib;
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
x_22 = l_Lake_instDataKindDynlib;
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
x_27 = lean_alloc_closure((void*)(l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___redArg___lam__0), 9, 7);
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
x_32 = l_Lake_instDataKindDynlib;
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
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_18; 
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_9, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_9, 0);
lean_inc(x_39);
lean_dec(x_9);
x_40 = !lean_is_exclusive(x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_38, 1);
x_42 = l_Lake_BuildTrace_mix(x_1, x_41);
x_43 = lean_apply_1(x_2, x_39);
lean_ctor_set(x_38, 1, x_42);
x_44 = lean_box(1);
x_45 = lean_unbox(x_44);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_46 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_43, x_45, x_3, x_4, x_5, x_6, x_7, x_38, x_10);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_ctor_get(x_48, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_string_utf8_byte_size(x_51);
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_nat_dec_eq(x_53, x_54);
if (x_55 == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_50);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_57 = lean_ctor_get(x_50, 0);
x_58 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_59 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_51, x_53, x_54);
x_60 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_51, x_59, x_53);
x_61 = lean_string_utf8_extract(x_51, x_59, x_60);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_51);
x_62 = lean_string_append(x_58, x_61);
lean_dec(x_61);
x_63 = lean_box(1);
x_64 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_64, 0, x_62);
x_65 = lean_unbox(x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_65);
x_66 = lean_box(0);
x_67 = lean_array_push(x_57, x_64);
lean_ctor_set(x_50, 0, x_67);
x_68 = l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__1(x_52, x_66, x_3, x_4, x_5, x_6, x_7, x_50, x_49);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = x_68;
goto block_37;
}
else
{
lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_69 = lean_ctor_get(x_50, 0);
x_70 = lean_ctor_get_uint8(x_50, sizeof(void*)*2);
x_71 = lean_ctor_get(x_50, 1);
lean_inc(x_71);
lean_inc(x_69);
lean_dec(x_50);
x_72 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_73 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_51, x_53, x_54);
x_74 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_51, x_73, x_53);
x_75 = lean_string_utf8_extract(x_51, x_73, x_74);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_51);
x_76 = lean_string_append(x_72, x_75);
lean_dec(x_75);
x_77 = lean_box(1);
x_78 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_78, 0, x_76);
x_79 = lean_unbox(x_77);
lean_ctor_set_uint8(x_78, sizeof(void*)*1, x_79);
x_80 = lean_box(0);
x_81 = lean_array_push(x_69, x_78);
x_82 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_71);
lean_ctor_set_uint8(x_82, sizeof(void*)*2, x_70);
x_83 = l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__1(x_52, x_80, x_3, x_4, x_5, x_6, x_7, x_82, x_49);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = x_83;
goto block_37;
}
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_53);
lean_dec(x_51);
x_84 = lean_box(0);
x_85 = l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__1(x_52, x_84, x_3, x_4, x_5, x_6, x_7, x_50, x_49);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = x_85;
goto block_37;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_86 = lean_ctor_get(x_46, 1);
lean_inc(x_86);
lean_dec(x_46);
x_87 = lean_ctor_get(x_47, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_47, 1);
lean_inc(x_88);
lean_dec(x_47);
x_11 = x_87;
x_12 = x_88;
x_13 = x_86;
goto block_17;
}
}
else
{
lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; 
x_89 = lean_ctor_get(x_38, 0);
x_90 = lean_ctor_get_uint8(x_38, sizeof(void*)*2);
x_91 = lean_ctor_get(x_38, 1);
lean_inc(x_91);
lean_inc(x_89);
lean_dec(x_38);
x_92 = l_Lake_BuildTrace_mix(x_1, x_91);
x_93 = lean_apply_1(x_2, x_39);
x_94 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_94, 0, x_89);
lean_ctor_set(x_94, 1, x_92);
lean_ctor_set_uint8(x_94, sizeof(void*)*2, x_90);
x_95 = lean_box(1);
x_96 = lean_unbox(x_95);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_97 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_93, x_96, x_3, x_4, x_5, x_6, x_7, x_94, x_10);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_ctor_get(x_99, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
lean_dec(x_99);
x_104 = lean_string_utf8_byte_size(x_102);
x_105 = lean_unsigned_to_nat(0u);
x_106 = lean_nat_dec_eq(x_104, x_105);
if (x_106 == 0)
{
lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_107 = lean_ctor_get(x_101, 0);
lean_inc(x_107);
x_108 = lean_ctor_get_uint8(x_101, sizeof(void*)*2);
x_109 = lean_ctor_get(x_101, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_110 = x_101;
} else {
 lean_dec_ref(x_101);
 x_110 = lean_box(0);
}
x_111 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_112 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_102, x_104, x_105);
x_113 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_102, x_112, x_104);
x_114 = lean_string_utf8_extract(x_102, x_112, x_113);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_102);
x_115 = lean_string_append(x_111, x_114);
lean_dec(x_114);
x_116 = lean_box(1);
x_117 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_117, 0, x_115);
x_118 = lean_unbox(x_116);
lean_ctor_set_uint8(x_117, sizeof(void*)*1, x_118);
x_119 = lean_box(0);
x_120 = lean_array_push(x_107, x_117);
if (lean_is_scalar(x_110)) {
 x_121 = lean_alloc_ctor(0, 2, 1);
} else {
 x_121 = x_110;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_109);
lean_ctor_set_uint8(x_121, sizeof(void*)*2, x_108);
x_122 = l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__1(x_103, x_119, x_3, x_4, x_5, x_6, x_7, x_121, x_100);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = x_122;
goto block_37;
}
else
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_104);
lean_dec(x_102);
x_123 = lean_box(0);
x_124 = l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__1(x_103, x_123, x_3, x_4, x_5, x_6, x_7, x_101, x_100);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = x_124;
goto block_37;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_125 = lean_ctor_get(x_97, 1);
lean_inc(x_125);
lean_dec(x_97);
x_126 = lean_ctor_get(x_98, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_98, 1);
lean_inc(x_127);
lean_dec(x_98);
x_11 = x_126;
x_12 = x_127;
x_13 = x_125;
goto block_17;
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_9);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_task_pure(x_9);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_10);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_131 = lean_ctor_get(x_9, 0);
x_132 = lean_ctor_get(x_9, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_9);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_task_pure(x_133);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_10);
return x_135;
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
block_37:
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__0), 2, 1);
lean_closure_set(x_25, 0, x_23);
x_26 = lean_box(1);
x_27 = lean_unbox(x_26);
x_28 = lean_task_map(x_25, x_24, x_8, x_27);
lean_ctor_set(x_18, 0, x_28);
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_dec(x_18);
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_dec(x_19);
x_31 = lean_ctor_get(x_20, 0);
lean_inc(x_31);
lean_dec(x_20);
x_32 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__0), 2, 1);
lean_closure_set(x_32, 0, x_30);
x_33 = lean_box(1);
x_34 = lean_unbox(x_33);
x_35 = lean_task_map(x_32, x_31, x_8, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_29);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_15 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__2), 10, 8);
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
x_19 = l_Lake_instDataKindDynlib;
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
x_22 = l_Lake_instDataKindDynlib;
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
x_27 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__2), 10, 8);
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
x_32 = l_Lake_instDataKindDynlib;
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
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(x_1, x_6);
x_17 = l_Array_append___redArg(x_16, x_2);
x_18 = l_Array_append___redArg(x_17, x_3);
x_19 = l_Lake_compileSharedLib(x_4, x_18, x_5, x_15, x_13);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_20, 1);
lean_ctor_set(x_12, 0, x_24);
lean_ctor_set(x_20, 1, x_12);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
lean_ctor_set(x_12, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_12);
lean_ctor_set(x_19, 0, x_27);
return x_19;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_ctor_get(x_20, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_31 = x_20;
} else {
 lean_dec_ref(x_20);
 x_31 = lean_box(0);
}
lean_ctor_set(x_12, 0, x_30);
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_12);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_28);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_19);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_19, 0);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_20);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_20, 1);
lean_ctor_set(x_12, 0, x_37);
lean_ctor_set(x_20, 1, x_12);
return x_19;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_20, 0);
x_39 = lean_ctor_get(x_20, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_20);
lean_ctor_set(x_12, 0, x_39);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_12);
lean_ctor_set(x_19, 0, x_40);
return x_19;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_19, 1);
lean_inc(x_41);
lean_dec(x_19);
x_42 = lean_ctor_get(x_20, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_20, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_44 = x_20;
} else {
 lean_dec_ref(x_20);
 x_44 = lean_box(0);
}
lean_ctor_set(x_12, 0, x_43);
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_12);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
return x_46;
}
}
}
else
{
lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_12, 0);
x_48 = lean_ctor_get_uint8(x_12, sizeof(void*)*2);
x_49 = lean_ctor_get(x_12, 1);
lean_inc(x_49);
lean_inc(x_47);
lean_dec(x_12);
x_50 = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(x_1, x_6);
x_51 = l_Array_append___redArg(x_50, x_2);
x_52 = l_Array_append___redArg(x_51, x_3);
x_53 = l_Lake_compileSharedLib(x_4, x_52, x_5, x_47, x_13);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_56 = x_53;
} else {
 lean_dec_ref(x_53);
 x_56 = lean_box(0);
}
x_57 = lean_ctor_get(x_54, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_59 = x_54;
} else {
 lean_dec_ref(x_54);
 x_59 = lean_box(0);
}
x_60 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_49);
lean_ctor_set_uint8(x_60, sizeof(void*)*2, x_48);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_57);
lean_ctor_set(x_61, 1, x_60);
if (lean_is_scalar(x_56)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_56;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_55);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_63 = lean_ctor_get(x_53, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_64 = x_53;
} else {
 lean_dec_ref(x_53);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_54, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_54, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_67 = x_54;
} else {
 lean_dec_ref(x_54);
 x_67 = lean_box(0);
}
x_68 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_49);
lean_ctor_set_uint8(x_68, sizeof(void*)*2, x_48);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_65);
lean_ctor_set(x_69, 1, x_68);
if (lean_is_scalar(x_64)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_64;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_63);
return x_70;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (x_1 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_mk_empty_array_with_capacity(x_2);
x_13 = lean_apply_8(x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(x_4, x_10, x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_apply_8(x_3, x_17, x_5, x_6, x_7, x_8, x_9, x_18, x_16);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_14, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_ctor_get(x_15, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_29 = x_15;
} else {
 lean_dec_ref(x_15);
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
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint64_t x_16; uint64_t x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_174 = 1723;
x_175 = lean_unsigned_to_nat(0u);
x_176 = lean_array_get_size(x_1);
x_177 = lean_nat_dec_lt(x_175, x_176);
if (x_177 == 0)
{
lean_dec(x_176);
x_16 = x_174;
goto block_173;
}
else
{
uint8_t x_178; 
x_178 = lean_nat_dec_le(x_176, x_176);
if (x_178 == 0)
{
lean_dec(x_176);
x_16 = x_174;
goto block_173;
}
else
{
size_t x_179; size_t x_180; uint64_t x_181; 
x_179 = 0;
x_180 = lean_usize_of_nat(x_176);
lean_dec(x_176);
x_181 = l_Array_foldlMUnsafe_fold___at___Lake_buildLeanO_spec__0(x_1, x_179, x_180, x_174);
x_16 = x_181;
goto block_173;
}
}
block_173:
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_18 = lean_ctor_get(x_14, 1);
x_19 = l_Lake_buildO___lam__2___closed__0;
x_20 = l_Lake_buildO___lam__2___closed__1;
x_21 = lean_array_to_list(x_1);
x_22 = l_List_toString___at___Lean_rewriteManualLinksCore_rw_spec__0(x_21);
lean_dec(x_21);
x_23 = lean_string_append(x_20, x_22);
lean_dec(x_22);
x_24 = lean_string_append(x_19, x_23);
lean_dec(x_23);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Lake_platformTrace___closed__2;
x_27 = l_Lake_platformTrace___closed__4;
x_28 = lean_box_uint64(x_16);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_27);
x_30 = l_Lake_BuildTrace_mix(x_18, x_29);
x_31 = l_Lake_platformTrace;
x_32 = l_Lake_BuildTrace_mix(x_30, x_31);
lean_ctor_set(x_14, 1, x_32);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_33 = lean_apply_7(x_2, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
lean_dec(x_34);
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_35, 1);
x_40 = l_Lake_BuildTrace_mix(x_39, x_37);
lean_ctor_set(x_35, 1, x_40);
x_41 = lean_box(x_3);
lean_inc(x_8);
x_42 = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__1___boxed), 11, 4);
lean_closure_set(x_42, 0, x_41);
lean_closure_set(x_42, 1, x_25);
lean_closure_set(x_42, 2, x_4);
lean_closure_set(x_42, 3, x_8);
x_43 = lean_box(0);
x_44 = l_Lake_sharedLibExt;
x_45 = lean_unbox(x_43);
x_46 = l_Lake_buildArtifactUnlessUpToDate(x_5, x_42, x_45, x_44, x_6, x_9, x_10, x_11, x_12, x_13, x_35, x_36);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_46);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_46, 0);
lean_dec(x_49);
x_50 = !lean_is_exclusive(x_47);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_47, 0);
x_52 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_7);
lean_ctor_set(x_52, 2, x_8);
lean_ctor_set_uint8(x_52, sizeof(void*)*3, x_6);
lean_ctor_set(x_47, 0, x_52);
return x_46;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_47, 0);
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_47);
x_55 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_7);
lean_ctor_set(x_55, 2, x_8);
lean_ctor_set_uint8(x_55, sizeof(void*)*3, x_6);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
lean_ctor_set(x_46, 0, x_56);
return x_46;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_46, 1);
lean_inc(x_57);
lean_dec(x_46);
x_58 = lean_ctor_get(x_47, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_47, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_60 = x_47;
} else {
 lean_dec_ref(x_47);
 x_60 = lean_box(0);
}
x_61 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_7);
lean_ctor_set(x_61, 2, x_8);
lean_ctor_set_uint8(x_61, sizeof(void*)*3, x_6);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_57);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_8);
lean_dec(x_7);
x_64 = !lean_is_exclusive(x_46);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_46, 0);
lean_dec(x_65);
x_66 = !lean_is_exclusive(x_47);
if (x_66 == 0)
{
return x_46;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_47, 0);
x_68 = lean_ctor_get(x_47, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_47);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set(x_46, 0, x_69);
return x_46;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_46, 1);
lean_inc(x_70);
lean_dec(x_46);
x_71 = lean_ctor_get(x_47, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_47, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_73 = x_47;
} else {
 lean_dec_ref(x_47);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_70);
return x_75;
}
}
}
else
{
lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; 
x_76 = lean_ctor_get(x_35, 0);
x_77 = lean_ctor_get_uint8(x_35, sizeof(void*)*2);
x_78 = lean_ctor_get(x_35, 1);
lean_inc(x_78);
lean_inc(x_76);
lean_dec(x_35);
x_79 = l_Lake_BuildTrace_mix(x_78, x_37);
x_80 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set_uint8(x_80, sizeof(void*)*2, x_77);
x_81 = lean_box(x_3);
lean_inc(x_8);
x_82 = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__1___boxed), 11, 4);
lean_closure_set(x_82, 0, x_81);
lean_closure_set(x_82, 1, x_25);
lean_closure_set(x_82, 2, x_4);
lean_closure_set(x_82, 3, x_8);
x_83 = lean_box(0);
x_84 = l_Lake_sharedLibExt;
x_85 = lean_unbox(x_83);
x_86 = l_Lake_buildArtifactUnlessUpToDate(x_5, x_82, x_85, x_84, x_6, x_9, x_10, x_11, x_12, x_13, x_80, x_36);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_89 = x_86;
} else {
 lean_dec_ref(x_86);
 x_89 = lean_box(0);
}
x_90 = lean_ctor_get(x_87, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_87, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_92 = x_87;
} else {
 lean_dec_ref(x_87);
 x_92 = lean_box(0);
}
x_93 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_7);
lean_ctor_set(x_93, 2, x_8);
lean_ctor_set_uint8(x_93, sizeof(void*)*3, x_6);
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_92;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
if (lean_is_scalar(x_89)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_89;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_88);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_8);
lean_dec(x_7);
x_96 = lean_ctor_get(x_86, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_97 = x_86;
} else {
 lean_dec_ref(x_86);
 x_97 = lean_box(0);
}
x_98 = lean_ctor_get(x_87, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_87, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_100 = x_87;
} else {
 lean_dec_ref(x_87);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
if (lean_is_scalar(x_97)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_97;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_96);
return x_102;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_103 = !lean_is_exclusive(x_33);
if (x_103 == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_ctor_get(x_33, 0);
lean_dec(x_104);
x_105 = !lean_is_exclusive(x_34);
if (x_105 == 0)
{
return x_33;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_34, 0);
x_107 = lean_ctor_get(x_34, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_34);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set(x_33, 0, x_108);
return x_33;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_109 = lean_ctor_get(x_33, 1);
lean_inc(x_109);
lean_dec(x_33);
x_110 = lean_ctor_get(x_34, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_34, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_112 = x_34;
} else {
 lean_dec_ref(x_34);
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
lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_115 = lean_ctor_get(x_14, 0);
x_116 = lean_ctor_get_uint8(x_14, sizeof(void*)*2);
x_117 = lean_ctor_get(x_14, 1);
lean_inc(x_117);
lean_inc(x_115);
lean_dec(x_14);
x_118 = l_Lake_buildO___lam__2___closed__0;
x_119 = l_Lake_buildO___lam__2___closed__1;
x_120 = lean_array_to_list(x_1);
x_121 = l_List_toString___at___Lean_rewriteManualLinksCore_rw_spec__0(x_120);
lean_dec(x_120);
x_122 = lean_string_append(x_119, x_121);
lean_dec(x_121);
x_123 = lean_string_append(x_118, x_122);
lean_dec(x_122);
x_124 = lean_unsigned_to_nat(0u);
x_125 = l_Lake_platformTrace___closed__2;
x_126 = l_Lake_platformTrace___closed__4;
x_127 = lean_box_uint64(x_16);
x_128 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_128, 0, x_123);
lean_ctor_set(x_128, 1, x_125);
lean_ctor_set(x_128, 2, x_127);
lean_ctor_set(x_128, 3, x_126);
x_129 = l_Lake_BuildTrace_mix(x_117, x_128);
x_130 = l_Lake_platformTrace;
x_131 = l_Lake_BuildTrace_mix(x_129, x_130);
x_132 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_132, 0, x_115);
lean_ctor_set(x_132, 1, x_131);
lean_ctor_set_uint8(x_132, sizeof(void*)*2, x_116);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_133 = lean_apply_7(x_2, x_9, x_10, x_11, x_12, x_13, x_132, x_15);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; 
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
lean_dec(x_133);
x_137 = lean_ctor_get(x_134, 0);
lean_inc(x_137);
lean_dec(x_134);
x_138 = lean_ctor_get(x_135, 0);
lean_inc(x_138);
x_139 = lean_ctor_get_uint8(x_135, sizeof(void*)*2);
x_140 = lean_ctor_get(x_135, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_141 = x_135;
} else {
 lean_dec_ref(x_135);
 x_141 = lean_box(0);
}
x_142 = l_Lake_BuildTrace_mix(x_140, x_137);
if (lean_is_scalar(x_141)) {
 x_143 = lean_alloc_ctor(0, 2, 1);
} else {
 x_143 = x_141;
}
lean_ctor_set(x_143, 0, x_138);
lean_ctor_set(x_143, 1, x_142);
lean_ctor_set_uint8(x_143, sizeof(void*)*2, x_139);
x_144 = lean_box(x_3);
lean_inc(x_8);
x_145 = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__1___boxed), 11, 4);
lean_closure_set(x_145, 0, x_144);
lean_closure_set(x_145, 1, x_124);
lean_closure_set(x_145, 2, x_4);
lean_closure_set(x_145, 3, x_8);
x_146 = lean_box(0);
x_147 = l_Lake_sharedLibExt;
x_148 = lean_unbox(x_146);
x_149 = l_Lake_buildArtifactUnlessUpToDate(x_5, x_145, x_148, x_147, x_6, x_9, x_10, x_11, x_12, x_13, x_143, x_136);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_152 = x_149;
} else {
 lean_dec_ref(x_149);
 x_152 = lean_box(0);
}
x_153 = lean_ctor_get(x_150, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_150, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_155 = x_150;
} else {
 lean_dec_ref(x_150);
 x_155 = lean_box(0);
}
x_156 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_7);
lean_ctor_set(x_156, 2, x_8);
lean_ctor_set_uint8(x_156, sizeof(void*)*3, x_6);
if (lean_is_scalar(x_155)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_155;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_154);
if (lean_is_scalar(x_152)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_152;
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_151);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_8);
lean_dec(x_7);
x_159 = lean_ctor_get(x_149, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_160 = x_149;
} else {
 lean_dec_ref(x_149);
 x_160 = lean_box(0);
}
x_161 = lean_ctor_get(x_150, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_150, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_163 = x_150;
} else {
 lean_dec_ref(x_150);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
if (lean_is_scalar(x_160)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_160;
}
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_159);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_166 = lean_ctor_get(x_133, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_167 = x_133;
} else {
 lean_dec_ref(x_133);
 x_167 = lean_box(0);
}
x_168 = lean_ctor_get(x_134, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_134, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_170 = x_134;
} else {
 lean_dec_ref(x_134);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_169);
if (lean_is_scalar(x_167)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_167;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_166);
return x_172;
}
}
}
}
}
static lean_object* _init_l_Lake_buildSharedLib___lam__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("linkLibs", 8, 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; uint8_t x_29; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_inc(x_3);
lean_inc(x_2);
x_19 = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__0___boxed), 13, 5);
lean_closure_set(x_19, 0, x_10);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_2);
lean_closure_set(x_19, 3, x_3);
lean_closure_set(x_19, 4, x_4);
x_20 = lean_box(x_6);
x_21 = lean_box(x_7);
x_22 = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__2___boxed), 15, 7);
lean_closure_set(x_22, 0, x_2);
lean_closure_set(x_22, 1, x_5);
lean_closure_set(x_22, 2, x_20);
lean_closure_set(x_22, 3, x_19);
lean_closure_set(x_22, 4, x_3);
lean_closure_set(x_22, 5, x_21);
lean_closure_set(x_22, 6, x_8);
x_23 = l_Lake_buildSharedLib___lam__3___closed__0;
x_24 = l_Lake_Job_collectArray___redArg(x_9, x_23);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_box(0);
x_27 = lean_unbox(x_26);
x_28 = l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___redArg(x_24, x_22, x_25, x_27, x_11, x_12, x_13, x_14, x_15, x_18, x_17);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_16);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_28, 0);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_28);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_16);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
static lean_object* _init_l_Lake_buildSharedLib___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("linkObjs", 8, 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_18 = lean_box(x_10);
x_19 = lean_box(x_9);
x_20 = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__3___boxed), 17, 9);
lean_closure_set(x_20, 0, x_5);
lean_closure_set(x_20, 1, x_6);
lean_closure_set(x_20, 2, x_2);
lean_closure_set(x_20, 3, x_7);
lean_closure_set(x_20, 4, x_8);
lean_closure_set(x_20, 5, x_18);
lean_closure_set(x_20, 6, x_19);
lean_closure_set(x_20, 7, x_1);
lean_closure_set(x_20, 8, x_4);
x_21 = l_Lake_buildSharedLib___closed__0;
x_22 = l_Lake_Job_collectArray___redArg(x_3, x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_box(1);
x_25 = lean_unbox(x_24);
x_26 = l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg(x_22, x_20, x_23, x_25, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___redArg(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lake_buildSharedLib___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = l_Lake_buildSharedLib___lam__1(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = l_Lake_buildSharedLib___lam__2(x_1, x_2, x_16, x_4, x_5, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__3___boxed(lean_object** _args) {
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
uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_unbox(x_6);
lean_dec(x_6);
x_19 = lean_unbox(x_7);
lean_dec(x_7);
x_20 = l_Lake_buildSharedLib___lam__3(x_1, x_2, x_3, x_4, x_5, x_18, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_9);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___boxed(lean_object** _args) {
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
uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_unbox(x_9);
lean_dec(x_9);
x_19 = lean_unbox(x_10);
lean_dec(x_10);
x_20 = l_Lake_buildSharedLib(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18, x_19, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_3);
return x_20;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLib___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1;
x_2 = l_Lake_buildLeanO___lam__0___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
if (x_5 == 0)
{
lean_object* x_90; 
x_90 = lean_mk_empty_array_with_capacity(x_6);
x_18 = x_90;
x_19 = x_13;
x_20 = x_14;
goto block_89;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(x_7, x_13, x_14);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
x_18 = x_94;
x_19 = x_95;
x_20 = x_93;
goto block_89;
}
else
{
uint8_t x_96; 
lean_dec(x_17);
lean_dec(x_4);
x_96 = !lean_is_exclusive(x_91);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_91, 0);
lean_dec(x_97);
x_98 = !lean_is_exclusive(x_92);
if (x_98 == 0)
{
return x_91;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_92, 0);
x_100 = lean_ctor_get(x_92, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_92);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set(x_91, 0, x_101);
return x_91;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_102 = lean_ctor_get(x_91, 1);
lean_inc(x_102);
lean_dec(x_91);
x_103 = lean_ctor_get(x_92, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_92, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_105 = x_92;
} else {
 lean_dec_ref(x_92);
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
block_89:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_17, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_17, 12);
lean_inc(x_22);
x_23 = lean_ctor_get(x_17, 18);
lean_inc(x_23);
lean_dec(x_17);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(x_1, x_18);
lean_dec(x_18);
x_27 = l_Array_append___redArg(x_26, x_2);
x_28 = l_Array_append___redArg(x_27, x_3);
x_29 = l_Lake_buildLeanSharedLib___lam__0___closed__0;
x_30 = lean_array_push(x_29, x_21);
x_31 = l_Array_append___redArg(x_28, x_30);
lean_dec(x_30);
x_32 = l_Array_append___redArg(x_31, x_23);
lean_dec(x_23);
x_33 = l_Lake_compileSharedLib(x_4, x_32, x_22, x_25, x_20);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_33, 0);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_34, 1);
lean_ctor_set(x_19, 0, x_38);
lean_ctor_set(x_34, 1, x_19);
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_34, 0);
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_34);
lean_ctor_set(x_19, 0, x_40);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_19);
lean_ctor_set(x_33, 0, x_41);
return x_33;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_33, 1);
lean_inc(x_42);
lean_dec(x_33);
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_45 = x_34;
} else {
 lean_dec_ref(x_34);
 x_45 = lean_box(0);
}
lean_ctor_set(x_19, 0, x_44);
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_19);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_42);
return x_47;
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_33);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_33, 0);
lean_dec(x_49);
x_50 = !lean_is_exclusive(x_34);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_34, 1);
lean_ctor_set(x_19, 0, x_51);
lean_ctor_set(x_34, 1, x_19);
return x_33;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_34, 0);
x_53 = lean_ctor_get(x_34, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_34);
lean_ctor_set(x_19, 0, x_53);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_19);
lean_ctor_set(x_33, 0, x_54);
return x_33;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_33, 1);
lean_inc(x_55);
lean_dec(x_33);
x_56 = lean_ctor_get(x_34, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_34, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_58 = x_34;
} else {
 lean_dec_ref(x_34);
 x_58 = lean_box(0);
}
lean_ctor_set(x_19, 0, x_57);
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_19);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_55);
return x_60;
}
}
}
else
{
lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_61 = lean_ctor_get(x_19, 0);
x_62 = lean_ctor_get_uint8(x_19, sizeof(void*)*2);
x_63 = lean_ctor_get(x_19, 1);
lean_inc(x_63);
lean_inc(x_61);
lean_dec(x_19);
x_64 = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(x_1, x_18);
lean_dec(x_18);
x_65 = l_Array_append___redArg(x_64, x_2);
x_66 = l_Array_append___redArg(x_65, x_3);
x_67 = l_Lake_buildLeanSharedLib___lam__0___closed__0;
x_68 = lean_array_push(x_67, x_21);
x_69 = l_Array_append___redArg(x_66, x_68);
lean_dec(x_68);
x_70 = l_Array_append___redArg(x_69, x_23);
lean_dec(x_23);
x_71 = l_Lake_compileSharedLib(x_4, x_70, x_22, x_61, x_20);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_74 = x_71;
} else {
 lean_dec_ref(x_71);
 x_74 = lean_box(0);
}
x_75 = lean_ctor_get(x_72, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_77 = x_72;
} else {
 lean_dec_ref(x_72);
 x_77 = lean_box(0);
}
x_78 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_63);
lean_ctor_set_uint8(x_78, sizeof(void*)*2, x_62);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_78);
if (lean_is_scalar(x_74)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_74;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_73);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_81 = lean_ctor_get(x_71, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_82 = x_71;
} else {
 lean_dec_ref(x_71);
 x_82 = lean_box(0);
}
x_83 = lean_ctor_get(x_72, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_72, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_85 = x_72;
} else {
 lean_dec_ref(x_72);
 x_85 = lean_box(0);
}
x_86 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_63);
lean_ctor_set_uint8(x_86, sizeof(void*)*2, x_62);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_83);
lean_ctor_set(x_87, 1, x_86);
if (lean_is_scalar(x_82)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_82;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_81);
return x_88;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint64_t x_22; uint64_t x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get_uint8(x_14, sizeof(void*)*2);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_19 = x_14;
} else {
 lean_dec_ref(x_14);
 x_19 = lean_box(0);
}
x_20 = lean_ctor_get(x_13, 2);
lean_inc(x_20);
x_21 = l_Lake_BuildTrace_mix(x_18, x_20);
x_74 = 1723;
x_75 = lean_unsigned_to_nat(0u);
x_76 = lean_array_get_size(x_1);
x_77 = lean_nat_dec_lt(x_75, x_76);
if (x_77 == 0)
{
lean_dec(x_76);
x_22 = x_74;
goto block_73;
}
else
{
uint8_t x_78; 
x_78 = lean_nat_dec_le(x_76, x_76);
if (x_78 == 0)
{
lean_dec(x_76);
x_22 = x_74;
goto block_73;
}
else
{
size_t x_79; size_t x_80; uint64_t x_81; 
x_79 = 0;
x_80 = lean_usize_of_nat(x_76);
lean_dec(x_76);
x_81 = l_Array_foldlMUnsafe_fold___at___Lake_buildLeanO_spec__0(x_1, x_79, x_80, x_74);
x_22 = x_81;
goto block_73;
}
}
block_73:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; 
x_23 = l_Lake_buildO___lam__2___closed__0;
x_24 = l_Lake_buildO___lam__2___closed__1;
lean_inc(x_1);
x_25 = lean_array_to_list(x_1);
x_26 = l_List_toString___at___Lean_rewriteManualLinksCore_rw_spec__0(x_25);
lean_dec(x_25);
x_27 = lean_string_append(x_24, x_26);
lean_dec(x_26);
x_28 = lean_string_append(x_23, x_27);
lean_dec(x_27);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_box(x_5);
lean_inc(x_8);
lean_inc(x_4);
x_31 = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__0___boxed), 14, 7);
lean_closure_set(x_31, 0, x_2);
lean_closure_set(x_31, 1, x_3);
lean_closure_set(x_31, 2, x_1);
lean_closure_set(x_31, 3, x_4);
lean_closure_set(x_31, 4, x_30);
lean_closure_set(x_31, 5, x_29);
lean_closure_set(x_31, 6, x_8);
x_32 = l_Lake_platformTrace___closed__2;
x_33 = l_Lake_platformTrace___closed__4;
x_34 = lean_box_uint64(x_22);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_32);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set(x_35, 3, x_33);
x_36 = l_Lake_BuildTrace_mix(x_21, x_35);
x_37 = l_Lake_platformTrace;
x_38 = l_Lake_BuildTrace_mix(x_36, x_37);
if (lean_is_scalar(x_19)) {
 x_39 = lean_alloc_ctor(0, 2, 1);
} else {
 x_39 = x_19;
}
lean_ctor_set(x_39, 0, x_16);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*2, x_17);
x_40 = lean_box(0);
x_41 = l_Lake_sharedLibExt;
x_42 = lean_unbox(x_40);
x_43 = l_Lake_buildArtifactUnlessUpToDate(x_4, x_31, x_42, x_41, x_6, x_9, x_10, x_11, x_12, x_13, x_39, x_15);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_43);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_43, 0);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_44);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_44, 0);
x_49 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_7);
lean_ctor_set(x_49, 2, x_8);
lean_ctor_set_uint8(x_49, sizeof(void*)*3, x_6);
lean_ctor_set(x_44, 0, x_49);
return x_43;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_44, 0);
x_51 = lean_ctor_get(x_44, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_44);
x_52 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_7);
lean_ctor_set(x_52, 2, x_8);
lean_ctor_set_uint8(x_52, sizeof(void*)*3, x_6);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set(x_43, 0, x_53);
return x_43;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_43, 1);
lean_inc(x_54);
lean_dec(x_43);
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
x_58 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_7);
lean_ctor_set(x_58, 2, x_8);
lean_ctor_set_uint8(x_58, sizeof(void*)*3, x_6);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_54);
return x_60;
}
}
else
{
uint8_t x_61; 
lean_dec(x_8);
lean_dec(x_7);
x_61 = !lean_is_exclusive(x_43);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_43, 0);
lean_dec(x_62);
x_63 = !lean_is_exclusive(x_44);
if (x_63 == 0)
{
return x_43;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_44, 0);
x_65 = lean_ctor_get(x_44, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_44);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_43, 0, x_66);
return x_43;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_43, 1);
lean_inc(x_67);
lean_dec(x_43);
x_68 = lean_ctor_get(x_44, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_44, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_70 = x_44;
} else {
 lean_dec_ref(x_44);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_67);
return x_72;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; uint8_t x_26; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_17 = lean_box(x_4);
x_18 = lean_box(x_5);
x_19 = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__1___boxed), 15, 7);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_8);
lean_closure_set(x_19, 2, x_2);
lean_closure_set(x_19, 3, x_3);
lean_closure_set(x_19, 4, x_17);
lean_closure_set(x_19, 5, x_18);
lean_closure_set(x_19, 6, x_6);
x_20 = l_Lake_buildSharedLib___lam__3___closed__0;
x_21 = l_Lake_Job_collectArray___redArg(x_7, x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_box(0);
x_24 = lean_unbox(x_23);
x_25 = l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___redArg(x_21, x_19, x_22, x_24, x_9, x_10, x_11, x_12, x_13, x_16, x_15);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_14);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_14);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_16 = lean_box(x_8);
x_17 = lean_box(x_7);
x_18 = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__2___boxed), 15, 7);
lean_closure_set(x_18, 0, x_6);
lean_closure_set(x_18, 1, x_5);
lean_closure_set(x_18, 2, x_2);
lean_closure_set(x_18, 3, x_16);
lean_closure_set(x_18, 4, x_17);
lean_closure_set(x_18, 5, x_1);
lean_closure_set(x_18, 6, x_4);
x_19 = l_Lake_buildSharedLib___closed__0;
x_20 = l_Lake_Job_collectArray___redArg(x_3, x_19);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_box(1);
x_23 = lean_unbox(x_22);
x_24 = l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg(x_20, x_18, x_21, x_23, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Lake_buildLeanSharedLib___lam__0(x_1, x_2, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = l_Lake_buildLeanSharedLib___lam__1(x_1, x_2, x_3, x_4, x_16, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_4);
lean_dec(x_4);
x_17 = lean_unbox(x_5);
lean_dec(x_5);
x_18 = l_Lake_buildLeanSharedLib___lam__2(x_1, x_2, x_3, x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_7);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_7);
lean_dec(x_7);
x_17 = lean_unbox(x_8);
lean_dec(x_8);
x_18 = l_Lake_buildLeanSharedLib(x_1, x_2, x_3, x_4, x_5, x_6, x_16, x_17, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_3);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_18; 
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_9, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_9, 0);
lean_inc(x_39);
lean_dec(x_9);
x_40 = !lean_is_exclusive(x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_38, 1);
x_42 = l_Lake_BuildTrace_mix(x_1, x_41);
x_43 = lean_apply_1(x_2, x_39);
lean_ctor_set(x_38, 1, x_42);
x_44 = lean_box(1);
x_45 = lean_unbox(x_44);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_46 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_43, x_45, x_3, x_4, x_5, x_6, x_7, x_38, x_10);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_ctor_get(x_48, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_string_utf8_byte_size(x_51);
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_nat_dec_eq(x_53, x_54);
if (x_55 == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_50);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_57 = lean_ctor_get(x_50, 0);
x_58 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_59 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_51, x_53, x_54);
x_60 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_51, x_59, x_53);
x_61 = lean_string_utf8_extract(x_51, x_59, x_60);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_51);
x_62 = lean_string_append(x_58, x_61);
lean_dec(x_61);
x_63 = lean_box(1);
x_64 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_64, 0, x_62);
x_65 = lean_unbox(x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_65);
x_66 = lean_box(0);
x_67 = lean_array_push(x_57, x_64);
lean_ctor_set(x_50, 0, x_67);
x_68 = l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__1(x_52, x_66, x_3, x_4, x_5, x_6, x_7, x_50, x_49);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = x_68;
goto block_37;
}
else
{
lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_69 = lean_ctor_get(x_50, 0);
x_70 = lean_ctor_get_uint8(x_50, sizeof(void*)*2);
x_71 = lean_ctor_get(x_50, 1);
lean_inc(x_71);
lean_inc(x_69);
lean_dec(x_50);
x_72 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_73 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_51, x_53, x_54);
x_74 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_51, x_73, x_53);
x_75 = lean_string_utf8_extract(x_51, x_73, x_74);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_51);
x_76 = lean_string_append(x_72, x_75);
lean_dec(x_75);
x_77 = lean_box(1);
x_78 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_78, 0, x_76);
x_79 = lean_unbox(x_77);
lean_ctor_set_uint8(x_78, sizeof(void*)*1, x_79);
x_80 = lean_box(0);
x_81 = lean_array_push(x_69, x_78);
x_82 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_71);
lean_ctor_set_uint8(x_82, sizeof(void*)*2, x_70);
x_83 = l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__1(x_52, x_80, x_3, x_4, x_5, x_6, x_7, x_82, x_49);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = x_83;
goto block_37;
}
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_53);
lean_dec(x_51);
x_84 = lean_box(0);
x_85 = l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__1(x_52, x_84, x_3, x_4, x_5, x_6, x_7, x_50, x_49);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = x_85;
goto block_37;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_86 = lean_ctor_get(x_46, 1);
lean_inc(x_86);
lean_dec(x_46);
x_87 = lean_ctor_get(x_47, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_47, 1);
lean_inc(x_88);
lean_dec(x_47);
x_11 = x_87;
x_12 = x_88;
x_13 = x_86;
goto block_17;
}
}
else
{
lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; 
x_89 = lean_ctor_get(x_38, 0);
x_90 = lean_ctor_get_uint8(x_38, sizeof(void*)*2);
x_91 = lean_ctor_get(x_38, 1);
lean_inc(x_91);
lean_inc(x_89);
lean_dec(x_38);
x_92 = l_Lake_BuildTrace_mix(x_1, x_91);
x_93 = lean_apply_1(x_2, x_39);
x_94 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_94, 0, x_89);
lean_ctor_set(x_94, 1, x_92);
lean_ctor_set_uint8(x_94, sizeof(void*)*2, x_90);
x_95 = lean_box(1);
x_96 = lean_unbox(x_95);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_97 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_93, x_96, x_3, x_4, x_5, x_6, x_7, x_94, x_10);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_ctor_get(x_99, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
lean_dec(x_99);
x_104 = lean_string_utf8_byte_size(x_102);
x_105 = lean_unsigned_to_nat(0u);
x_106 = lean_nat_dec_eq(x_104, x_105);
if (x_106 == 0)
{
lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_107 = lean_ctor_get(x_101, 0);
lean_inc(x_107);
x_108 = lean_ctor_get_uint8(x_101, sizeof(void*)*2);
x_109 = lean_ctor_get(x_101, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_110 = x_101;
} else {
 lean_dec_ref(x_101);
 x_110 = lean_box(0);
}
x_111 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_112 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_102, x_104, x_105);
x_113 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_102, x_112, x_104);
x_114 = lean_string_utf8_extract(x_102, x_112, x_113);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_102);
x_115 = lean_string_append(x_111, x_114);
lean_dec(x_114);
x_116 = lean_box(1);
x_117 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_117, 0, x_115);
x_118 = lean_unbox(x_116);
lean_ctor_set_uint8(x_117, sizeof(void*)*1, x_118);
x_119 = lean_box(0);
x_120 = lean_array_push(x_107, x_117);
if (lean_is_scalar(x_110)) {
 x_121 = lean_alloc_ctor(0, 2, 1);
} else {
 x_121 = x_110;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_109);
lean_ctor_set_uint8(x_121, sizeof(void*)*2, x_108);
x_122 = l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__1(x_103, x_119, x_3, x_4, x_5, x_6, x_7, x_121, x_100);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = x_122;
goto block_37;
}
else
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_104);
lean_dec(x_102);
x_123 = lean_box(0);
x_124 = l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__1(x_103, x_123, x_3, x_4, x_5, x_6, x_7, x_101, x_100);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = x_124;
goto block_37;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_125 = lean_ctor_get(x_97, 1);
lean_inc(x_125);
lean_dec(x_97);
x_126 = lean_ctor_get(x_98, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_98, 1);
lean_inc(x_127);
lean_dec(x_98);
x_11 = x_126;
x_12 = x_127;
x_13 = x_125;
goto block_17;
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_9);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_task_pure(x_9);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_10);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_131 = lean_ctor_get(x_9, 0);
x_132 = lean_ctor_get(x_9, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_9);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_task_pure(x_133);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_10);
return x_135;
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
block_37:
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(x_25, 0, x_23);
x_26 = lean_box(1);
x_27 = lean_unbox(x_26);
x_28 = lean_task_map(x_25, x_24, x_8, x_27);
lean_ctor_set(x_18, 0, x_28);
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_dec(x_18);
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_dec(x_19);
x_31 = lean_ctor_get(x_20, 0);
lean_inc(x_31);
lean_dec(x_20);
x_32 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(x_32, 0, x_30);
x_33 = lean_box(1);
x_34 = lean_unbox(x_33);
x_35 = lean_task_map(x_32, x_31, x_8, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_29);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_15 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__2), 10, 8);
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
x_19 = l_Lake_instDataKindFilePath;
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
x_22 = l_Lake_instDataKindFilePath;
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
x_27 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__2), 10, 8);
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
x_32 = l_Lake_instDataKindFilePath;
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
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(x_1, x_12, x_13);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_16, 3);
lean_inc(x_22);
x_23 = lean_ctor_get(x_16, 12);
lean_inc(x_23);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(x_2, x_21);
lean_dec(x_21);
x_27 = l_Array_append___redArg(x_26, x_3);
x_28 = l_Array_append___redArg(x_27, x_4);
x_29 = l_Lake_buildLeanSharedLib___lam__0___closed__0;
x_30 = lean_array_push(x_29, x_22);
x_31 = l_Array_append___redArg(x_28, x_30);
lean_dec(x_30);
x_32 = l_Lake_LeanInstall_ccLinkFlags(x_5, x_16);
lean_dec(x_16);
x_33 = l_Array_append___redArg(x_31, x_32);
lean_dec(x_32);
x_34 = l_Lake_compileExe(x_6, x_33, x_23, x_25, x_20);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_34, 0);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_35, 1);
lean_ctor_set(x_19, 0, x_39);
lean_ctor_set(x_35, 1, x_19);
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_35, 0);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_35);
lean_ctor_set(x_19, 0, x_41);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_19);
lean_ctor_set(x_34, 0, x_42);
return x_34;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_34, 1);
lean_inc(x_43);
lean_dec(x_34);
x_44 = lean_ctor_get(x_35, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_35, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_46 = x_35;
} else {
 lean_dec_ref(x_35);
 x_46 = lean_box(0);
}
lean_ctor_set(x_19, 0, x_45);
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_19);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_43);
return x_48;
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_34);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_34, 0);
lean_dec(x_50);
x_51 = !lean_is_exclusive(x_35);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_35, 1);
lean_ctor_set(x_19, 0, x_52);
lean_ctor_set(x_35, 1, x_19);
return x_34;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_35, 0);
x_54 = lean_ctor_get(x_35, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_35);
lean_ctor_set(x_19, 0, x_54);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_19);
lean_ctor_set(x_34, 0, x_55);
return x_34;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_34, 1);
lean_inc(x_56);
lean_dec(x_34);
x_57 = lean_ctor_get(x_35, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_35, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_59 = x_35;
} else {
 lean_dec_ref(x_35);
 x_59 = lean_box(0);
}
lean_ctor_set(x_19, 0, x_58);
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_19);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_56);
return x_61;
}
}
}
else
{
lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_62 = lean_ctor_get(x_19, 0);
x_63 = lean_ctor_get_uint8(x_19, sizeof(void*)*2);
x_64 = lean_ctor_get(x_19, 1);
lean_inc(x_64);
lean_inc(x_62);
lean_dec(x_19);
x_65 = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(x_2, x_21);
lean_dec(x_21);
x_66 = l_Array_append___redArg(x_65, x_3);
x_67 = l_Array_append___redArg(x_66, x_4);
x_68 = l_Lake_buildLeanSharedLib___lam__0___closed__0;
x_69 = lean_array_push(x_68, x_22);
x_70 = l_Array_append___redArg(x_67, x_69);
lean_dec(x_69);
x_71 = l_Lake_LeanInstall_ccLinkFlags(x_5, x_16);
lean_dec(x_16);
x_72 = l_Array_append___redArg(x_70, x_71);
lean_dec(x_71);
x_73 = l_Lake_compileExe(x_6, x_72, x_23, x_62, x_20);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
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
x_77 = lean_ctor_get(x_74, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_79 = x_74;
} else {
 lean_dec_ref(x_74);
 x_79 = lean_box(0);
}
x_80 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_64);
lean_ctor_set_uint8(x_80, sizeof(void*)*2, x_63);
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_79;
}
lean_ctor_set(x_81, 0, x_77);
lean_ctor_set(x_81, 1, x_80);
if (lean_is_scalar(x_76)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_76;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_75);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_83 = lean_ctor_get(x_73, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_84 = x_73;
} else {
 lean_dec_ref(x_73);
 x_84 = lean_box(0);
}
x_85 = lean_ctor_get(x_74, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_74, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_87 = x_74;
} else {
 lean_dec_ref(x_74);
 x_87 = lean_box(0);
}
x_88 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_64);
lean_ctor_set_uint8(x_88, sizeof(void*)*2, x_63);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_85);
lean_ctor_set(x_89, 1, x_88);
if (lean_is_scalar(x_84)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_84;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_83);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_16);
lean_dec(x_6);
x_91 = !lean_is_exclusive(x_17);
if (x_91 == 0)
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_ctor_get(x_17, 0);
lean_dec(x_92);
x_93 = !lean_is_exclusive(x_18);
if (x_93 == 0)
{
return x_17;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_18, 0);
x_95 = lean_ctor_get(x_18, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_18);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set(x_17, 0, x_96);
return x_17;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_97 = lean_ctor_get(x_17, 1);
lean_inc(x_97);
lean_dec(x_17);
x_98 = lean_ctor_get(x_18, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_18, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_100 = x_18;
} else {
 lean_dec_ref(x_18);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_97);
return x_102;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint64_t x_22; uint64_t x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_12, sizeof(void*)*2);
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
x_18 = lean_ctor_get(x_11, 2);
lean_inc(x_18);
x_19 = lean_box(x_4);
lean_inc(x_5);
lean_inc(x_3);
x_20 = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__0___boxed), 13, 6);
lean_closure_set(x_20, 0, x_6);
lean_closure_set(x_20, 1, x_1);
lean_closure_set(x_20, 2, x_2);
lean_closure_set(x_20, 3, x_3);
lean_closure_set(x_20, 4, x_19);
lean_closure_set(x_20, 5, x_5);
x_21 = l_Lake_BuildTrace_mix(x_16, x_18);
x_43 = 1723;
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_array_get_size(x_3);
x_46 = lean_nat_dec_lt(x_44, x_45);
if (x_46 == 0)
{
lean_dec(x_45);
x_22 = x_43;
goto block_42;
}
else
{
uint8_t x_47; 
x_47 = lean_nat_dec_le(x_45, x_45);
if (x_47 == 0)
{
lean_dec(x_45);
x_22 = x_43;
goto block_42;
}
else
{
size_t x_48; size_t x_49; uint64_t x_50; 
x_48 = 0;
x_49 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_50 = l_Array_foldlMUnsafe_fold___at___Lake_buildLeanO_spec__0(x_3, x_48, x_49, x_43);
x_22 = x_50;
goto block_42;
}
}
block_42:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; 
x_23 = l_Lake_buildO___lam__2___closed__0;
x_24 = l_Lake_buildO___lam__2___closed__1;
x_25 = lean_array_to_list(x_3);
x_26 = l_List_toString___at___Lean_rewriteManualLinksCore_rw_spec__0(x_25);
lean_dec(x_25);
x_27 = lean_string_append(x_24, x_26);
lean_dec(x_26);
x_28 = lean_string_append(x_23, x_27);
lean_dec(x_27);
x_29 = l_Lake_platformTrace___closed__2;
x_30 = l_Lake_platformTrace___closed__4;
x_31 = lean_box_uint64(x_22);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_32, 2, x_31);
lean_ctor_set(x_32, 3, x_30);
x_33 = l_Lake_BuildTrace_mix(x_21, x_32);
x_34 = l_Lake_platformTrace;
x_35 = l_Lake_BuildTrace_mix(x_33, x_34);
if (lean_is_scalar(x_17)) {
 x_36 = lean_alloc_ctor(0, 2, 1);
} else {
 x_36 = x_17;
}
lean_ctor_set(x_36, 0, x_14);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*2, x_15);
x_37 = lean_box(0);
x_38 = l_System_FilePath_exeExtension;
x_39 = lean_unbox(x_37);
x_40 = lean_unbox(x_37);
x_41 = l_Lake_buildArtifactUnlessUpToDate(x_5, x_20, x_39, x_38, x_40, x_7, x_8, x_9, x_10, x_11, x_36, x_13);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_15 = lean_box(x_3);
x_16 = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__1___boxed), 13, 5);
lean_closure_set(x_16, 0, x_6);
lean_closure_set(x_16, 1, x_1);
lean_closure_set(x_16, 2, x_2);
lean_closure_set(x_16, 3, x_15);
lean_closure_set(x_16, 4, x_4);
x_17 = l_Lake_buildSharedLib___lam__3___closed__0;
x_18 = l_Lake_Job_collectArray___redArg(x_5, x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_box(0);
x_21 = lean_unbox(x_20);
x_22 = l_Lake_Job_mapM___at___Lake_buildLeanO_spec__1___redArg(x_18, x_16, x_19, x_21, x_7, x_8, x_9, x_10, x_11, x_14, x_13);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_12);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_12);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_14 = lean_box(x_6);
x_15 = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__2___boxed), 13, 5);
lean_closure_set(x_15, 0, x_4);
lean_closure_set(x_15, 1, x_5);
lean_closure_set(x_15, 2, x_14);
lean_closure_set(x_15, 3, x_1);
lean_closure_set(x_15, 4, x_3);
x_16 = l_Lake_buildSharedLib___closed__0;
x_17 = l_Lake_Job_collectArray___redArg(x_2, x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_box(1);
x_20 = lean_unbox(x_19);
x_21 = l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg(x_17, x_15, x_18, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Lake_buildLeanExe___lam__0(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_Lake_buildLeanExe___lam__1(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lake_buildLeanExe___lam__2(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_6);
lean_dec(x_6);
x_15 = l_Lake_buildLeanExe(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_15;
}
}
lean_object* initialize_Lake_Config_Monad(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_JsonObject(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Target_Fetch(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Actions(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Job(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Common(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Monad(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_JsonObject(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Target_Fetch(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Actions(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Job(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instMonadWorkspaceJobM___closed__0 = _init_l_Lake_instMonadWorkspaceJobM___closed__0();
lean_mark_persistent(l_Lake_instMonadWorkspaceJobM___closed__0);
l_Lake_instMonadWorkspaceJobM___closed__1 = _init_l_Lake_instMonadWorkspaceJobM___closed__1();
lean_mark_persistent(l_Lake_instMonadWorkspaceJobM___closed__1);
l_Lake_instMonadWorkspaceJobM___closed__2 = _init_l_Lake_instMonadWorkspaceJobM___closed__2();
lean_mark_persistent(l_Lake_instMonadWorkspaceJobM___closed__2);
l_Lake_instMonadWorkspaceJobM___closed__3 = _init_l_Lake_instMonadWorkspaceJobM___closed__3();
lean_mark_persistent(l_Lake_instMonadWorkspaceJobM___closed__3);
l_Lake_instMonadWorkspaceJobM___closed__4 = _init_l_Lake_instMonadWorkspaceJobM___closed__4();
lean_mark_persistent(l_Lake_instMonadWorkspaceJobM___closed__4);
l_Lake_instMonadWorkspaceJobM___closed__5 = _init_l_Lake_instMonadWorkspaceJobM___closed__5();
lean_mark_persistent(l_Lake_instMonadWorkspaceJobM___closed__5);
l_Lake_instMonadWorkspaceJobM___closed__6 = _init_l_Lake_instMonadWorkspaceJobM___closed__6();
lean_mark_persistent(l_Lake_instMonadWorkspaceJobM___closed__6);
l_Lake_instMonadWorkspaceJobM___closed__7 = _init_l_Lake_instMonadWorkspaceJobM___closed__7();
lean_mark_persistent(l_Lake_instMonadWorkspaceJobM___closed__7);
l_Lake_instMonadWorkspaceJobM___closed__8 = _init_l_Lake_instMonadWorkspaceJobM___closed__8();
lean_mark_persistent(l_Lake_instMonadWorkspaceJobM___closed__8);
l_Lake_instMonadWorkspaceJobM___closed__9 = _init_l_Lake_instMonadWorkspaceJobM___closed__9();
lean_mark_persistent(l_Lake_instMonadWorkspaceJobM___closed__9);
l_Lake_instMonadWorkspaceJobM___closed__10 = _init_l_Lake_instMonadWorkspaceJobM___closed__10();
lean_mark_persistent(l_Lake_instMonadWorkspaceJobM___closed__10);
l_Lake_instMonadWorkspaceJobM___closed__11 = _init_l_Lake_instMonadWorkspaceJobM___closed__11();
lean_mark_persistent(l_Lake_instMonadWorkspaceJobM___closed__11);
l_Lake_instMonadWorkspaceJobM___closed__12 = _init_l_Lake_instMonadWorkspaceJobM___closed__12();
lean_mark_persistent(l_Lake_instMonadWorkspaceJobM___closed__12);
l_Lake_instMonadWorkspaceJobM___closed__13 = _init_l_Lake_instMonadWorkspaceJobM___closed__13();
lean_mark_persistent(l_Lake_instMonadWorkspaceJobM___closed__13);
l_Lake_instMonadWorkspaceJobM___closed__14 = _init_l_Lake_instMonadWorkspaceJobM___closed__14();
lean_mark_persistent(l_Lake_instMonadWorkspaceJobM___closed__14);
l_Lake_instMonadWorkspaceJobM___closed__15 = _init_l_Lake_instMonadWorkspaceJobM___closed__15();
lean_mark_persistent(l_Lake_instMonadWorkspaceJobM___closed__15);
l_Lake_instMonadWorkspaceJobM___closed__16 = _init_l_Lake_instMonadWorkspaceJobM___closed__16();
lean_mark_persistent(l_Lake_instMonadWorkspaceJobM___closed__16);
l_Lake_instMonadWorkspaceJobM___closed__17 = _init_l_Lake_instMonadWorkspaceJobM___closed__17();
lean_mark_persistent(l_Lake_instMonadWorkspaceJobM___closed__17);
l_Lake_instMonadWorkspaceJobM___closed__18 = _init_l_Lake_instMonadWorkspaceJobM___closed__18();
lean_mark_persistent(l_Lake_instMonadWorkspaceJobM___closed__18);
l_Lake_instMonadWorkspaceJobM___closed__19 = _init_l_Lake_instMonadWorkspaceJobM___closed__19();
lean_mark_persistent(l_Lake_instMonadWorkspaceJobM___closed__19);
l_Lake_instMonadWorkspaceJobM___closed__20 = _init_l_Lake_instMonadWorkspaceJobM___closed__20();
lean_mark_persistent(l_Lake_instMonadWorkspaceJobM___closed__20);
l_Lake_instMonadWorkspaceJobM = _init_l_Lake_instMonadWorkspaceJobM();
lean_mark_persistent(l_Lake_instMonadWorkspaceJobM);
l_Lake_instToJsonPUnit__lake = _init_l_Lake_instToJsonPUnit__lake();
lean_mark_persistent(l_Lake_instToJsonPUnit__lake);
l_Lake_noBuildCode = _init_l_Lake_noBuildCode();
l_Lake_platformTrace___closed__0 = _init_l_Lake_platformTrace___closed__0();
l_Lake_platformTrace___closed__1 = _init_l_Lake_platformTrace___closed__1();
l_Lake_platformTrace___closed__2 = _init_l_Lake_platformTrace___closed__2();
lean_mark_persistent(l_Lake_platformTrace___closed__2);
l_Lake_platformTrace___closed__3 = _init_l_Lake_platformTrace___closed__3();
lean_mark_persistent(l_Lake_platformTrace___closed__3);
l_Lake_platformTrace___closed__4 = _init_l_Lake_platformTrace___closed__4();
lean_mark_persistent(l_Lake_platformTrace___closed__4);
l_Lake_platformTrace___closed__5___boxed__const__1 = _init_l_Lake_platformTrace___closed__5___boxed__const__1();
lean_mark_persistent(l_Lake_platformTrace___closed__5___boxed__const__1);
l_Lake_platformTrace___closed__5 = _init_l_Lake_platformTrace___closed__5();
lean_mark_persistent(l_Lake_platformTrace___closed__5);
l_Lake_platformTrace = _init_l_Lake_platformTrace();
lean_mark_persistent(l_Lake_platformTrace);
l_Lake_addPureTrace___redArg___closed__0 = _init_l_Lake_addPureTrace___redArg___closed__0();
lean_mark_persistent(l_Lake_addPureTrace___redArg___closed__0);
l_Prod_toJson___at___Array_toJson___at_____private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178__spec__0_spec__0___closed__0 = _init_l_Prod_toJson___at___Array_toJson___at_____private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178__spec__0_spec__0___closed__0();
lean_mark_persistent(l_Prod_toJson___at___Array_toJson___at_____private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_178__spec__0_spec__0___closed__0);
l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata___closed__0____x40_Lake_Build_Common___hyg_178_ = _init_l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata___closed__0____x40_Lake_Build_Common___hyg_178_();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata___closed__0____x40_Lake_Build_Common___hyg_178_);
l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata___closed__1____x40_Lake_Build_Common___hyg_178_ = _init_l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata___closed__1____x40_Lake_Build_Common___hyg_178_();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata___closed__1____x40_Lake_Build_Common___hyg_178_);
l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata___closed__2____x40_Lake_Build_Common___hyg_178_ = _init_l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata___closed__2____x40_Lake_Build_Common___hyg_178_();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata___closed__2____x40_Lake_Build_Common___hyg_178_);
l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata___closed__3____x40_Lake_Build_Common___hyg_178_ = _init_l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata___closed__3____x40_Lake_Build_Common___hyg_178_();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata___closed__3____x40_Lake_Build_Common___hyg_178_);
l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata___closed__4____x40_Lake_Build_Common___hyg_178_ = _init_l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata___closed__4____x40_Lake_Build_Common___hyg_178_();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata___closed__4____x40_Lake_Build_Common___hyg_178_);
l_Lake_instToJsonBuildMetadata___closed__0 = _init_l_Lake_instToJsonBuildMetadata___closed__0();
lean_mark_persistent(l_Lake_instToJsonBuildMetadata___closed__0);
l_Lake_instToJsonBuildMetadata = _init_l_Lake_instToJsonBuildMetadata();
lean_mark_persistent(l_Lake_instToJsonBuildMetadata);
l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0_spec__0___closed__0 = _init_l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0_spec__0___closed__0();
lean_mark_persistent(l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0_spec__0___closed__0);
l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0_spec__0___closed__1 = _init_l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0_spec__0___closed__1();
lean_mark_persistent(l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0_spec__0___closed__1);
l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0___closed__0 = _init_l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0___closed__0();
lean_mark_persistent(l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0___closed__0);
l_Option_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__3_spec__3___closed__0 = _init_l_Option_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__3_spec__3___closed__0();
lean_mark_persistent(l_Option_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__3_spec__3___closed__0);
l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__3___closed__0 = _init_l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__3___closed__0();
lean_mark_persistent(l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__3___closed__0);
l_Prod_fromJson_x3f___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5_spec__5_spec__5___closed__0 = _init_l_Prod_fromJson_x3f___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5_spec__5_spec__5___closed__0();
lean_mark_persistent(l_Prod_fromJson_x3f___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5_spec__5_spec__5___closed__0);
l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5___closed__0 = _init_l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5___closed__0();
lean_mark_persistent(l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5___closed__0);
l_Lake_BuildMetadata_fromJson_x3f___closed__0 = _init_l_Lake_BuildMetadata_fromJson_x3f___closed__0();
lean_mark_persistent(l_Lake_BuildMetadata_fromJson_x3f___closed__0);
l_Lake_BuildMetadata_fromJson_x3f___closed__1 = _init_l_Lake_BuildMetadata_fromJson_x3f___closed__1();
lean_mark_persistent(l_Lake_BuildMetadata_fromJson_x3f___closed__1);
l_Lake_BuildMetadata_fromJson_x3f___closed__2 = _init_l_Lake_BuildMetadata_fromJson_x3f___closed__2();
lean_mark_persistent(l_Lake_BuildMetadata_fromJson_x3f___closed__2);
l_Lake_BuildMetadata_fromJson_x3f___closed__3 = _init_l_Lake_BuildMetadata_fromJson_x3f___closed__3();
lean_mark_persistent(l_Lake_BuildMetadata_fromJson_x3f___closed__3);
l_Lake_BuildMetadata_fromJson_x3f___closed__4 = _init_l_Lake_BuildMetadata_fromJson_x3f___closed__4();
lean_mark_persistent(l_Lake_BuildMetadata_fromJson_x3f___closed__4);
l_Lake_BuildMetadata_fromJson_x3f___closed__5 = _init_l_Lake_BuildMetadata_fromJson_x3f___closed__5();
lean_mark_persistent(l_Lake_BuildMetadata_fromJson_x3f___closed__5);
l_Lake_BuildMetadata_fromJson_x3f___closed__6 = _init_l_Lake_BuildMetadata_fromJson_x3f___closed__6();
lean_mark_persistent(l_Lake_BuildMetadata_fromJson_x3f___closed__6);
l_Lake_BuildMetadata_fromJson_x3f___closed__7 = _init_l_Lake_BuildMetadata_fromJson_x3f___closed__7();
lean_mark_persistent(l_Lake_BuildMetadata_fromJson_x3f___closed__7);
l_Lake_instFromJsonBuildMetadata___closed__0 = _init_l_Lake_instFromJsonBuildMetadata___closed__0();
lean_mark_persistent(l_Lake_instFromJsonBuildMetadata___closed__0);
l_Lake_instFromJsonBuildMetadata = _init_l_Lake_instFromJsonBuildMetadata();
lean_mark_persistent(l_Lake_instFromJsonBuildMetadata);
l_Lake_readTraceFile___closed__0 = _init_l_Lake_readTraceFile___closed__0();
lean_mark_persistent(l_Lake_readTraceFile___closed__0);
l_Lake_readTraceFile___closed__1 = _init_l_Lake_readTraceFile___closed__1();
lean_mark_persistent(l_Lake_readTraceFile___closed__1);
l_Lake_checkHashUpToDate___redArg___closed__0 = _init_l_Lake_checkHashUpToDate___redArg___closed__0();
lean_mark_persistent(l_Lake_checkHashUpToDate___redArg___closed__0);
l_Lake_buildAction___redArg___closed__0 = _init_l_Lake_buildAction___redArg___closed__0();
l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0 = _init_l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0();
lean_mark_persistent(l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0);
l_Lake_writeFileHash___closed__0 = _init_l_Lake_writeFileHash___closed__0();
lean_mark_persistent(l_Lake_writeFileHash___closed__0);
l_Lake_buildFileUnlessUpToDate_x27___closed__0 = _init_l_Lake_buildFileUnlessUpToDate_x27___closed__0();
lean_mark_persistent(l_Lake_buildFileUnlessUpToDate_x27___closed__0);
l_Lake_resolveArtifactsUsing_x3f___redArg___closed__0 = _init_l_Lake_resolveArtifactsUsing_x3f___redArg___closed__0();
lean_mark_persistent(l_Lake_resolveArtifactsUsing_x3f___redArg___closed__0);
l_Lake_resolveArtifactsUsing_x3f___redArg___closed__1 = _init_l_Lake_resolveArtifactsUsing_x3f___redArg___closed__1();
lean_mark_persistent(l_Lake_resolveArtifactsUsing_x3f___redArg___closed__1);
l_Lake_resolveArtifactsUsing_x3f___redArg___closed__2 = _init_l_Lake_resolveArtifactsUsing_x3f___redArg___closed__2();
lean_mark_persistent(l_Lake_resolveArtifactsUsing_x3f___redArg___closed__2);
l_Lake_buildArtifactUnlessUpToDate___closed__0 = _init_l_Lake_buildArtifactUnlessUpToDate___closed__0();
lean_mark_persistent(l_Lake_buildArtifactUnlessUpToDate___closed__0);
l_Lake_buildArtifactUnlessUpToDate___closed__1 = _init_l_Lake_buildArtifactUnlessUpToDate___closed__1();
lean_mark_persistent(l_Lake_buildArtifactUnlessUpToDate___closed__1);
l_Lake_buildArtifactUnlessUpToDate___closed__2 = _init_l_Lake_buildArtifactUnlessUpToDate___closed__2();
lean_mark_persistent(l_Lake_buildArtifactUnlessUpToDate___closed__2);
l_Lake_buildArtifactUnlessUpToDate___closed__3 = _init_l_Lake_buildArtifactUnlessUpToDate___closed__3();
lean_mark_persistent(l_Lake_buildArtifactUnlessUpToDate___closed__3);
l_Lake_buildArtifactUnlessUpToDate___closed__4 = _init_l_Lake_buildArtifactUnlessUpToDate___closed__4();
lean_mark_persistent(l_Lake_buildArtifactUnlessUpToDate___closed__4);
l_Lake_buildArtifactUnlessUpToDate___closed__5 = _init_l_Lake_buildArtifactUnlessUpToDate___closed__5();
lean_mark_persistent(l_Lake_buildArtifactUnlessUpToDate___closed__5);
l_Lake_buildArtifactUnlessUpToDate___closed__6 = _init_l_Lake_buildArtifactUnlessUpToDate___closed__6();
lean_mark_persistent(l_Lake_buildArtifactUnlessUpToDate___closed__6);
l_Lake_buildArtifactUnlessUpToDate___closed__7 = _init_l_Lake_buildArtifactUnlessUpToDate___closed__7();
lean_mark_persistent(l_Lake_buildArtifactUnlessUpToDate___closed__7);
l_Lake_buildArtifactUnlessUpToDate___closed__8 = _init_l_Lake_buildArtifactUnlessUpToDate___closed__8();
lean_mark_persistent(l_Lake_buildArtifactUnlessUpToDate___closed__8);
l_Lake_buildArtifactUnlessUpToDate___closed__9 = _init_l_Lake_buildArtifactUnlessUpToDate___closed__9();
lean_mark_persistent(l_Lake_buildArtifactUnlessUpToDate___closed__9);
l_Lake_buildArtifactUnlessUpToDate___closed__10 = _init_l_Lake_buildArtifactUnlessUpToDate___closed__10();
lean_mark_persistent(l_Lake_buildArtifactUnlessUpToDate___closed__10);
l_Lake_buildArtifactUnlessUpToDate___closed__11 = _init_l_Lake_buildArtifactUnlessUpToDate___closed__11();
lean_mark_persistent(l_Lake_buildArtifactUnlessUpToDate___closed__11);
l_Lake_buildArtifactUnlessUpToDate___closed__12 = _init_l_Lake_buildArtifactUnlessUpToDate___closed__12();
lean_mark_persistent(l_Lake_buildArtifactUnlessUpToDate___closed__12);
l_Lake_buildArtifactUnlessUpToDate___closed__13 = _init_l_Lake_buildArtifactUnlessUpToDate___closed__13();
lean_mark_persistent(l_Lake_buildArtifactUnlessUpToDate___closed__13);
l_Lake_buildFileAfterDep___redArg___lam__0___closed__0 = _init_l_Lake_buildFileAfterDep___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lake_buildFileAfterDep___redArg___lam__0___closed__0);
l_Lake_buildFileAfterDepList___redArg___closed__0 = _init_l_Lake_buildFileAfterDepList___redArg___closed__0();
lean_mark_persistent(l_Lake_buildFileAfterDepList___redArg___closed__0);
l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__0 = _init_l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__0();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__0);
l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__1 = _init_l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__1();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__1);
l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__2 = _init_l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__2();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__2);
l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__3 = _init_l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__3();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__3);
l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__4 = _init_l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__4();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__4);
l_Lake_inputBinFile___redArg___lam__1___closed__0 = _init_l_Lake_inputBinFile___redArg___lam__1___closed__0();
lean_mark_persistent(l_Lake_inputBinFile___redArg___lam__1___closed__0);
l_Lake_inputBinFile___redArg___closed__0 = _init_l_Lake_inputBinFile___redArg___closed__0();
lean_mark_persistent(l_Lake_inputBinFile___redArg___closed__0);
l_Lake_inputBinFile___redArg___closed__1 = _init_l_Lake_inputBinFile___redArg___closed__1();
lean_mark_persistent(l_Lake_inputBinFile___redArg___closed__1);
l_Lake_inputBinFile___redArg___closed__2 = _init_l_Lake_inputBinFile___redArg___closed__2();
lean_mark_persistent(l_Lake_inputBinFile___redArg___closed__2);
l_Lake_inputBinFile___redArg___closed__3 = _init_l_Lake_inputBinFile___redArg___closed__3();
lean_mark_persistent(l_Lake_inputBinFile___redArg___closed__3);
l_Array_filterMapM___at___Lake_inputDir_spec__1___closed__0 = _init_l_Array_filterMapM___at___Lake_inputDir_spec__1___closed__0();
lean_mark_persistent(l_Array_filterMapM___at___Lake_inputDir_spec__1___closed__0);
l_Lake_buildO___lam__2___closed__0 = _init_l_Lake_buildO___lam__2___closed__0();
lean_mark_persistent(l_Lake_buildO___lam__2___closed__0);
l_Lake_buildO___lam__2___closed__1 = _init_l_Lake_buildO___lam__2___closed__1();
lean_mark_persistent(l_Lake_buildO___lam__2___closed__1);
l_Lake_buildO___lam__2___closed__2 = _init_l_Lake_buildO___lam__2___closed__2();
lean_mark_persistent(l_Lake_buildO___lam__2___closed__2);
l_Lake_buildO___lam__2___boxed__const__1 = _init_l_Lake_buildO___lam__2___boxed__const__1();
lean_mark_persistent(l_Lake_buildO___lam__2___boxed__const__1);
l_Lake_buildO___closed__0 = _init_l_Lake_buildO___closed__0();
lean_mark_persistent(l_Lake_buildO___closed__0);
l_Lake_buildLeanO___lam__0___closed__0 = _init_l_Lake_buildLeanO___lam__0___closed__0();
lean_mark_persistent(l_Lake_buildLeanO___lam__0___closed__0);
l_Lake_buildLeanO___lam__0___closed__1 = _init_l_Lake_buildLeanO___lam__0___closed__1();
lean_mark_persistent(l_Lake_buildLeanO___lam__0___closed__1);
l_Lake_buildLeanO___lam__0___closed__2 = _init_l_Lake_buildLeanO___lam__0___closed__2();
lean_mark_persistent(l_Lake_buildLeanO___lam__0___closed__2);
l_Lake_buildStaticLib___lam__1___closed__0 = _init_l_Lake_buildStaticLib___lam__1___closed__0();
lean_mark_persistent(l_Lake_buildStaticLib___lam__1___closed__0);
l_Lake_buildStaticLib___closed__0 = _init_l_Lake_buildStaticLib___closed__0();
lean_mark_persistent(l_Lake_buildStaticLib___closed__0);
l_Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0 = _init_l_Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0);
l_Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1);
l_List_mapTR_loop___at___Lake_formatCycle___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1_spec__1___closed__0 = _init_l_List_mapTR_loop___at___Lake_formatCycle___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1_spec__1___closed__0();
lean_mark_persistent(l_List_mapTR_loop___at___Lake_formatCycle___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1_spec__1___closed__0);
l_Lake_formatCycle___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1___closed__0 = _init_l_Lake_formatCycle___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1___closed__0();
lean_mark_persistent(l_Lake_formatCycle___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1___closed__0);
l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0 = _init_l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0);
l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1 = _init_l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1);
l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2 = _init_l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2);
l_Lake_buildSharedLib___lam__3___closed__0 = _init_l_Lake_buildSharedLib___lam__3___closed__0();
lean_mark_persistent(l_Lake_buildSharedLib___lam__3___closed__0);
l_Lake_buildSharedLib___closed__0 = _init_l_Lake_buildSharedLib___closed__0();
lean_mark_persistent(l_Lake_buildSharedLib___closed__0);
l_Lake_buildLeanSharedLib___lam__0___closed__0 = _init_l_Lake_buildLeanSharedLib___lam__0___closed__0();
lean_mark_persistent(l_Lake_buildLeanSharedLib___lam__0___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

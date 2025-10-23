// Lean compiler output
// Module: Lake.Build.Common
// Imports: public import Lake.Build.Job.Monad public import Lake.Config.Monad public import Lake.Util.JsonObject import Lake.Util.IO import Lake.Build.Target.Fetch public import Lake.Build.Actions
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
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_invalid_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___Lake_inputBinFile_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_read(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_toJson___at___Lake_BuildMetadata_toJson_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_readTraceFile_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(lean_object*, lean_object*);
lean_object* l_Lake_compileO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonArtifact___lam__0(lean_object*);
static lean_object* l_Lake_buildO___closed__0;
static lean_object* l_Lake_buildO___lam__2___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___at___Lake_buildArtifactUnlessUpToDate_spec__1(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t);
static lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__6_spec__6_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildSharedLib___lam__3___closed__0;
LEAN_EXPORT lean_object* l_Lake_OutputStatus_noConfusion___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeFileHash(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_inputBinFile_spec__7___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instFromJsonBuildMetadata___closed__0;
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ctorIdx___boxed(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_toJson___closed__7;
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldl___at___List_toString___at___Lake_buildLeanO_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Array_toJson___at___Lake_BuildMetadata_toJson_spec__4(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs___boxed(lean_object*, lean_object*);
lean_object* l_System_FilePath_walkDir(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildFileAfterDep___redArg___lam__0___closed__0;
static lean_object* l_List_mapTR_loop___at___Lake_formatCycle___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1_spec__1___closed__0;
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileHash(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatCycle___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ok_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addLeanTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at___Lake_buildLeanO_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___List_toString___at___Lake_buildLeanO_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_mapM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
lean_object* l_Lake_Cache_getArtifact___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__4(lean_object*);
static lean_object* l_Lake_buildStaticLib___closed__0;
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_writeFile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_inputBinFile_spec__6(lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stdout(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_toJson___at___Lake_BuildMetadata_toJson_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_inputBinFile_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__10;
lean_object* l_Lake_compileSharedLib(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_byte_array_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* l_Lake_JsonObject_insertJson(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4;
static lean_object* l_Lake_buildLeanO___lam__0___closed__1;
static lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__10;
LEAN_EXPORT lean_object* l_List_elem___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_serializeInputs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lake_computeTextFileHash(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_inputDir_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate(uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_JsonObject_getJson_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__14;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__3;
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_metadata(lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___redArg(lean_object*);
lean_object* l_Lake_Hash_ofDecimal_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPureTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofHashCheck(uint8_t);
static lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__6;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static uint64_t l_Lake_platformTrace___closed__1;
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadST(lean_object*);
extern lean_object* l_System_FilePath_exeExtension;
lean_object* l_Lake_Cache_writeOutputsCore(lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_buildLeanO_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToOutputJson_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l_Lake_platformTrace___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lake_EStateT_instPure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__6_spec__6_spec__7(size_t, size_t, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__0;
LEAN_EXPORT lean_object* l_Lake_OutputStatus_toCtorIdx___boxed(lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__13;
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonArtifact;
LEAN_EXPORT lean_object* l_Lake_buildLeanExe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___redArg(lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lake_ResolveOutputs_ctorIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0;
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__2___boxed(lean_object**);
uint64_t lean_string_hash(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_inputBinFile_spec__7(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_toString___at___Lake_buildLeanO_spec__0___closed__0;
lean_object* l_instMonadST___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_ofStub___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJson_x3f___lam__0(lean_object*, lean_object*);
lean_object* l_Lake_JobM_runFetchM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Cache_getArtifact(lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1;
static lean_object* l_Lake_getArtifacts_x3f___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_CacheMap_insertCore(uint64_t, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheEnabled___at___Lake_buildArtifactUnlessUpToDate_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
static lean_object* l_Lake_platformTrace___closed__7;
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofStub(uint64_t);
lean_object* l_Lake_instFromJsonLogEntry_fromJson(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Hash_hex(uint64_t);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0(lean_object*);
lean_object* l_instToStringString___lam__0___boxed(lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_readTraceFile_x3f(lean_object*, lean_object*);
lean_object* l_Lake_Dynlib_dir_x3f(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheEnabled___at___Lake_buildArtifactUnlessUpToDate_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildTrace_mix(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_compileExe(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJson_x3f___boxed(lean_object*);
lean_object* l_String_crlfToLf(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Cache_saveArtifact___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_IO_FS_writeBinFile(lean_object*, lean_object*);
static lean_object* l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__6___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_sharedLibExt;
LEAN_EXPORT lean_object* l_Lake_addPureTrace___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EIO_toBaseIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofHash(uint64_t);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_toJson___closed__3;
static lean_object* l_Lake_readTraceFile___closed__0;
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Prod_fromJson_x3f___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__6_spec__6_spec__6___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_platformTrace;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lake_instToOutputJsonArtifact___lam__0___closed__0;
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__2;
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_noConfusion___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_writeFileHash___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_inputBinFile___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofHashCheck___boxed(lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_noConfusion___redArg(uint8_t, uint8_t);
static lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now();
lean_object* lean_task_pure(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__4___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__0___boxed(lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__3;
static lean_object* l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__4___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___redArg(lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__0;
lean_object* l_Lake_createParentDirs(lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableEqOutputStatus(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instFunctor___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_System_FilePath_isDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceJobM;
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___Lake_inputTextFile_spec__0(lean_object*);
static lean_object* l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_ResolveOutputs_ctorIdx(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__0;
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__11;
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at_____private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__8;
extern lean_object* l_ByteArray_empty;
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_parse(lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
static lean_object* l_Lake_buildAction___redArg___closed__1;
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__12;
LEAN_EXPORT lean_object* l_Lake_readTraceFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__3___boxed(lean_object**);
static lean_object* l_Lake_buildSharedLib___lam__2___closed__0;
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__2(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion;
lean_object* l_Lake_Package_isArtifactCacheEnabled___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__1;
static lean_object* l_Lake_BuildMetadata_toJson___closed__1;
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFromJsonBuildMetadata;
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instAlternativeOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___at_____private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__1(lean_object*, lean_object*);
lean_object* l_Lake_removeFileIfExists(lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0(lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0;
static lean_object* l_Lake_platformTrace___closed__0;
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArtifact(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_collectArray___redArg(lean_object*, lean_object*);
static uint64_t l_Lake_platformTrace___closed__3;
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_toJson___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildO___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__0___closed__0;
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at_____private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0;
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_toJson___at___Lake_BuildMetadata_toJson_spec__3(lean_object*);
static lean_object* l_Lake_buildAction___redArg___closed__0;
extern lean_object* l_Lake_instDataKindFilePath;
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_inputBinFile___redArg___lam__1___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
static lean_object* l_Lake_buildSharedLib___closed__0;
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instPure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofHash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1___closed__0;
static lean_object* l_Lake_buildO___lam__2___closed__2;
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instAlternativeELogTOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheEnabled___at___Lake_buildArtifactUnlessUpToDate_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_JobState_merge(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofMTimeCheck(uint8_t);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__6_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Cache_readOutputs_x3f(lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at_____private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_instBEqOfDecidableEq___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__7;
static lean_object* l_Lake_inputBinFile___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__3___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_serializeInputs(lean_object*);
lean_object* l_Lake_copyFile(lean_object*, lean_object*);
static lean_object* l_List_toString___at___Lake_buildLeanO_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lake_cacheFileHash(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofFetch(uint64_t, lean_object*);
static lean_object* l_panic___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__3___closed__0;
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__17;
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildLeanExe___lam__1___closed__0;
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__6;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__6_spec__6(lean_object*);
static lean_object* l_Lake_platformTrace___closed__4;
static lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__7;
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_toJson___closed__4;
lean_object* l_Lake_BuildTrace_nil(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stderr(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__3___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EquipT_instFunctor___redArg(lean_object*);
static lean_object* l_Lake_buildLeanSharedLib___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t);
static lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0;
static lean_object* l_Lake_instToJsonBuildMetadata___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__15;
lean_object* l_Lake_ArtifactDescr_fromJson_x3f(lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_serializeInputs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_getArtifacts_x3f___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildLeanO___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_platformTrace___closed__6;
lean_object* l_Lake_Hash_ofJsonNumber_x3f(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__1;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeFileHash___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_toJson___closed__5;
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__3___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_IO_FS_instOrdSystemTime_ord(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_IO_FS_readFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonPUnit___lam__0(lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at_____private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__0(lean_object*, lean_object*);
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__1;
static lean_object* l_Lake_buildStaticLib___lam__1___closed__0;
static lean_object* l_Lake_BuildMetadata_toJson___closed__6;
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ok_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofStub___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__3___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPureTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___List_toString___at___Lake_buildLeanO_spec__0_spec__0(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lake_Hash_load_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_inputDir_spec__2(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_invalid_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Package_cacheScope(lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputFile(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildAction___at_____private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___Lake_inputTextFile_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__3___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___Lake_BuildMetadata_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1(uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJson_x3f___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__9;
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__1(size_t, size_t, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lake_EquipT_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern uint64_t l_Lake_Hash_nil;
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofFetch___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_toJson___at___Lake_BuildMetadata_toJson_spec__4_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_buildLeanO_spec__2(lean_object*, size_t, size_t, uint64_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheEnabled___at___Lake_buildArtifactUnlessUpToDate_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildFileUnlessUpToDate_x27___closed__0;
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonArtifact___lam__0___boxed(lean_object*);
static lean_object* l_Prod_toJson___at___Array_toJson___at___Lake_BuildMetadata_toJson_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildAction___at_____private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_instDataKindDynlib;
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___Lake_inputBinFile_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Artifact_trace(lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Option_toJson___at___Lake_BuildMetadata_toJson_spec__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofNat___boxed(lean_object*);
static lean_object* l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__1___closed__0;
LEAN_EXPORT lean_object* l_Lake_cacheArtifact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeTraceFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_addPureTrace___redArg___closed__0;
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArtifact___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeTraceFile___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__3___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_serializeInputs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Lake_OutputStatus_isCacheable(uint8_t);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__4;
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lake_formatCycle___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__4;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_get_set_stdin(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_readTraceFile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqOutputStatus___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__18;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_inputDir_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_LeanInstall_ccLinkFlags(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeTraceFile___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1;
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
uint8_t l_Lake_JobAction_merge(uint8_t, uint8_t);
LEAN_EXPORT uint64_t l_Lake_buildO___lam__0(uint64_t, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___redArg(lean_object*);
static lean_object* l_Lake_Cache_saveArtifact___closed__2;
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_toJson___at___Lake_BuildMetadata_toJson_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonBuildMetadata;
lean_object* l_String_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_inputDir_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_MTime_checkUpToDate___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_inputDir_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__20;
static lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__9;
LEAN_EXPORT lean_object* l_Lake_OutputStatus_isUpToDate___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_missing_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_toCtorIdx(uint8_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lake_compileStaticLib(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
static lean_object* l_Lake_buildLeanO___lam__0___closed__2;
lean_object* l_Lake_EStateT_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_OutputStatus_isUpToDate(uint8_t);
LEAN_EXPORT lean_object* l_Lake_writeTraceFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lake_writeFetchTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_computeBinFileHash(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lake_buildO___lam__2___closed__1;
static lean_object* l_Lake_BuildMetadata_toJson___closed__2;
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_inputDir_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArtifact___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_inputBinFile___redArg___closed__0;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__5;
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___redArg___boxed(lean_object*);
static lean_object* l_Lake_Cache_saveArtifact___closed__1;
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_writeFile(lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__16;
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__19;
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_addPureTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_isCacheable___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsArtifactOfMonadWorkspaceOfMonadLiftTBaseIOOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
static lean_object* l_Lake_formatCycle___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1___closed__0;
LEAN_EXPORT lean_object* l_Prod_toJson___at___Array_toJson___at___Lake_BuildMetadata_toJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lake_instDecidableEqHash___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_noConfusion___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_readBinFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToOutputJson_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsArtifactOfMonadWorkspaceOfMonadLiftTBaseIOOfMonad___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_inputDir___lam__1___closed__0;
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_clearFileHash___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_System_Platform_target;
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(uint64_t, lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonPUnit;
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_missing_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeFetchTrace(lean_object*, uint64_t, lean_object*);
lean_object* l_Lake_instToJsonLogEntry_toJson(lean_object*);
lean_object* l_IO_setAccessRights(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___at___Lake_buildArtifactUnlessUpToDate_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___boxed(lean_object**);
lean_object* l_Lake_instMonadLiftLakeMBuildTOfPure___redArg(lean_object*);
static lean_object* l_List_toString___at___Lake_buildLeanO_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___redArg___boxed(lean_object*);
static lean_object* l_Lake_platformTrace___closed__5;
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__4_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Hash_fromJson_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_clearFileHash(lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheFileHash___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at___Lake_buildLeanO_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_serializeInputs_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Option_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__4_spec__4___closed__0;
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJson_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at_____private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofMTimeCheck___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___redArg___boxed(lean_object*);
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadST(lean_box(0));
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
x_1 = lean_alloc_closure((void*)(l_instMonadST___lam__2___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instMonadWorkspaceJobM___closed__15;
x_2 = l_Lake_EStateT_instPure___redArg(x_1);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_instMonadWorkspaceJobM___closed__19;
x_2 = l_Lake_instMonadWorkspaceJobM___closed__16;
x_3 = l_Lake_instMonadLiftLakeMBuildTOfPure___redArg(x_2);
x_4 = lean_apply_2(x_3, lean_box(0), x_1);
return x_4;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
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
lean_inc_ref(x_11);
lean_inc(x_7);
x_13 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_13, 0, x_7);
lean_closure_set(x_13, 1, x_11);
lean_inc(x_7);
lean_inc_ref(x_6);
x_14 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_14, 0, x_6);
lean_closure_set(x_14, 1, x_7);
lean_closure_set(x_14, 2, x_5);
x_15 = l_Lake_EStateT_instFunctor___redArg(x_6);
x_16 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_16, 0, x_7);
lean_inc_ref(x_15);
lean_ctor_set(x_3, 4, x_12);
lean_ctor_set(x_3, 3, x_13);
lean_ctor_set(x_3, 2, x_14);
lean_ctor_set(x_3, 1, x_16);
lean_ctor_set(x_3, 0, x_15);
lean_ctor_set(x_1, 1, x_11);
lean_inc_ref(x_15);
x_17 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_17, 0, x_15);
x_18 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_18, 0, x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lake_instMonadWorkspaceJobM___closed__14;
lean_inc_ref(x_1);
x_21 = l_ReaderT_instAlternativeOfMonad___redArg(x_20, x_1);
x_22 = l_ReaderT_instMonad___redArg(x_1);
lean_inc_ref(x_22);
x_23 = l_ReaderT_instAlternativeOfMonad___redArg(x_21, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc_ref(x_24);
lean_dec_ref(x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_25);
lean_dec_ref(x_24);
x_26 = l_ReaderT_instMonad___redArg(x_22);
x_27 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_27);
x_28 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_28);
lean_dec_ref(x_27);
lean_inc_ref(x_28);
x_29 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_29, 0, x_28);
x_30 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_30, 0, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_ReaderT_instMonad___redArg(x_26);
x_33 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_33);
x_34 = lean_ctor_get(x_33, 0);
lean_inc_ref(x_34);
lean_dec_ref(x_33);
lean_inc_ref(x_34);
x_35 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_35, 0, x_34);
x_36 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_36, 0, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_inc_ref(x_37);
x_38 = l_Lake_EquipT_instFunctor___redArg(x_37);
x_39 = !lean_is_exclusive(x_32);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_40 = lean_ctor_get(x_32, 0);
x_41 = lean_ctor_get(x_32, 1);
lean_dec(x_41);
x_42 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_42);
lean_dec_ref(x_40);
x_43 = l_Lake_instMonadWorkspaceJobM___closed__20;
lean_inc_ref(x_19);
x_44 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_43, x_19);
x_45 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_44, x_19);
x_46 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(x_46, 0, lean_box(0));
lean_closure_set(x_46, 1, lean_box(0));
lean_closure_set(x_46, 2, lean_box(0));
lean_closure_set(x_46, 3, lean_box(0));
lean_closure_set(x_46, 4, x_45);
lean_inc_ref(x_25);
x_47 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_46, x_25);
x_48 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_47, x_25);
x_49 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_49, 0, lean_box(0));
lean_closure_set(x_49, 1, x_48);
lean_inc_ref(x_31);
x_50 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_49, x_31);
x_51 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_50, x_31);
x_52 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_52, 0, lean_box(0));
lean_closure_set(x_52, 1, x_51);
lean_inc_ref(x_37);
x_53 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_52, x_37);
x_54 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_53, x_37);
x_55 = lean_alloc_closure((void*)(l_Lake_EquipT_lift___boxed), 5, 4);
lean_closure_set(x_55, 0, lean_box(0));
lean_closure_set(x_55, 1, lean_box(0));
lean_closure_set(x_55, 2, lean_box(0));
lean_closure_set(x_55, 3, x_54);
lean_inc_ref(x_38);
x_56 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_55, x_38);
x_57 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_56, x_38);
x_58 = lean_alloc_closure((void*)(l_Lake_JobM_runFetchM___boxed), 9, 2);
lean_closure_set(x_58, 0, lean_box(0));
lean_closure_set(x_58, 1, x_57);
lean_inc_ref(x_42);
x_59 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_59, 0, x_42);
x_60 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_60, 0, x_42);
lean_ctor_set(x_32, 1, x_60);
lean_ctor_set(x_32, 0, x_59);
x_61 = l_Lake_EquipT_instFunctor___redArg(x_32);
x_62 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_58, x_61);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_63 = lean_ctor_get(x_32, 0);
lean_inc(x_63);
lean_dec(x_32);
x_64 = lean_ctor_get(x_63, 0);
lean_inc_ref(x_64);
lean_dec_ref(x_63);
x_65 = l_Lake_instMonadWorkspaceJobM___closed__20;
lean_inc_ref(x_19);
x_66 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_65, x_19);
x_67 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_66, x_19);
x_68 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(x_68, 0, lean_box(0));
lean_closure_set(x_68, 1, lean_box(0));
lean_closure_set(x_68, 2, lean_box(0));
lean_closure_set(x_68, 3, lean_box(0));
lean_closure_set(x_68, 4, x_67);
lean_inc_ref(x_25);
x_69 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_68, x_25);
x_70 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_69, x_25);
x_71 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_71, 0, lean_box(0));
lean_closure_set(x_71, 1, x_70);
lean_inc_ref(x_31);
x_72 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_71, x_31);
x_73 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_72, x_31);
x_74 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_74, 0, lean_box(0));
lean_closure_set(x_74, 1, x_73);
lean_inc_ref(x_37);
x_75 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_74, x_37);
x_76 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_75, x_37);
x_77 = lean_alloc_closure((void*)(l_Lake_EquipT_lift___boxed), 5, 4);
lean_closure_set(x_77, 0, lean_box(0));
lean_closure_set(x_77, 1, lean_box(0));
lean_closure_set(x_77, 2, lean_box(0));
lean_closure_set(x_77, 3, x_76);
lean_inc_ref(x_38);
x_78 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_77, x_38);
x_79 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_78, x_38);
x_80 = lean_alloc_closure((void*)(l_Lake_JobM_runFetchM___boxed), 9, 2);
lean_closure_set(x_80, 0, lean_box(0));
lean_closure_set(x_80, 1, x_79);
lean_inc_ref(x_64);
x_81 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_81, 0, x_64);
x_82 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_82, 0, x_64);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lake_EquipT_instFunctor___redArg(x_83);
x_85 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_80, x_84);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_86 = lean_ctor_get(x_1, 1);
x_87 = lean_ctor_get(x_3, 0);
x_88 = lean_ctor_get(x_3, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_3);
lean_inc(x_86);
lean_inc(x_88);
x_89 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_89, 0, x_88);
lean_closure_set(x_89, 1, x_86);
lean_inc(x_86);
lean_inc(x_88);
x_90 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_90, 0, x_88);
lean_closure_set(x_90, 1, x_86);
lean_inc_ref(x_89);
lean_inc(x_88);
x_91 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_91, 0, x_88);
lean_closure_set(x_91, 1, x_89);
lean_inc(x_88);
lean_inc_ref(x_87);
x_92 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_92, 0, x_87);
lean_closure_set(x_92, 1, x_88);
lean_closure_set(x_92, 2, x_86);
x_93 = l_Lake_EStateT_instFunctor___redArg(x_87);
x_94 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_94, 0, x_88);
lean_inc_ref(x_93);
x_95 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set(x_95, 2, x_92);
lean_ctor_set(x_95, 3, x_91);
lean_ctor_set(x_95, 4, x_90);
lean_ctor_set(x_1, 1, x_89);
lean_ctor_set(x_1, 0, x_95);
lean_inc_ref(x_93);
x_96 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_96, 0, x_93);
x_97 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_97, 0, x_93);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Lake_instMonadWorkspaceJobM___closed__14;
lean_inc_ref(x_1);
x_100 = l_ReaderT_instAlternativeOfMonad___redArg(x_99, x_1);
x_101 = l_ReaderT_instMonad___redArg(x_1);
lean_inc_ref(x_101);
x_102 = l_ReaderT_instAlternativeOfMonad___redArg(x_100, x_101);
x_103 = lean_ctor_get(x_102, 0);
lean_inc_ref(x_103);
lean_dec_ref(x_102);
x_104 = lean_ctor_get(x_103, 0);
lean_inc_ref(x_104);
lean_dec_ref(x_103);
x_105 = l_ReaderT_instMonad___redArg(x_101);
x_106 = lean_ctor_get(x_105, 0);
lean_inc_ref(x_106);
x_107 = lean_ctor_get(x_106, 0);
lean_inc_ref(x_107);
lean_dec_ref(x_106);
lean_inc_ref(x_107);
x_108 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_108, 0, x_107);
x_109 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_109, 0, x_107);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_ReaderT_instMonad___redArg(x_105);
x_112 = lean_ctor_get(x_111, 0);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_112, 0);
lean_inc_ref(x_113);
lean_dec_ref(x_112);
lean_inc_ref(x_113);
x_114 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_114, 0, x_113);
x_115 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_115, 0, x_113);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
lean_inc_ref(x_116);
x_117 = l_Lake_EquipT_instFunctor___redArg(x_116);
x_118 = lean_ctor_get(x_111, 0);
lean_inc_ref(x_118);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_119 = x_111;
} else {
 lean_dec_ref(x_111);
 x_119 = lean_box(0);
}
x_120 = lean_ctor_get(x_118, 0);
lean_inc_ref(x_120);
lean_dec_ref(x_118);
x_121 = l_Lake_instMonadWorkspaceJobM___closed__20;
lean_inc_ref(x_98);
x_122 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_121, x_98);
x_123 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_122, x_98);
x_124 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(x_124, 0, lean_box(0));
lean_closure_set(x_124, 1, lean_box(0));
lean_closure_set(x_124, 2, lean_box(0));
lean_closure_set(x_124, 3, lean_box(0));
lean_closure_set(x_124, 4, x_123);
lean_inc_ref(x_104);
x_125 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_124, x_104);
x_126 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_125, x_104);
x_127 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_127, 0, lean_box(0));
lean_closure_set(x_127, 1, x_126);
lean_inc_ref(x_110);
x_128 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_127, x_110);
x_129 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_128, x_110);
x_130 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_130, 0, lean_box(0));
lean_closure_set(x_130, 1, x_129);
lean_inc_ref(x_116);
x_131 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_130, x_116);
x_132 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_131, x_116);
x_133 = lean_alloc_closure((void*)(l_Lake_EquipT_lift___boxed), 5, 4);
lean_closure_set(x_133, 0, lean_box(0));
lean_closure_set(x_133, 1, lean_box(0));
lean_closure_set(x_133, 2, lean_box(0));
lean_closure_set(x_133, 3, x_132);
lean_inc_ref(x_117);
x_134 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_133, x_117);
x_135 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_134, x_117);
x_136 = lean_alloc_closure((void*)(l_Lake_JobM_runFetchM___boxed), 9, 2);
lean_closure_set(x_136, 0, lean_box(0));
lean_closure_set(x_136, 1, x_135);
lean_inc_ref(x_120);
x_137 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_137, 0, x_120);
x_138 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_138, 0, x_120);
if (lean_is_scalar(x_119)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_119;
}
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
x_140 = l_Lake_EquipT_instFunctor___redArg(x_139);
x_141 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_136, x_140);
return x_141;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_142 = lean_ctor_get(x_1, 0);
x_143 = lean_ctor_get(x_1, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_1);
x_144 = lean_ctor_get(x_142, 0);
lean_inc_ref(x_144);
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 lean_ctor_release(x_142, 2);
 lean_ctor_release(x_142, 3);
 lean_ctor_release(x_142, 4);
 x_146 = x_142;
} else {
 lean_dec_ref(x_142);
 x_146 = lean_box(0);
}
lean_inc(x_143);
lean_inc(x_145);
x_147 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_147, 0, x_145);
lean_closure_set(x_147, 1, x_143);
lean_inc(x_143);
lean_inc(x_145);
x_148 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_148, 0, x_145);
lean_closure_set(x_148, 1, x_143);
lean_inc_ref(x_147);
lean_inc(x_145);
x_149 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_149, 0, x_145);
lean_closure_set(x_149, 1, x_147);
lean_inc(x_145);
lean_inc_ref(x_144);
x_150 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_150, 0, x_144);
lean_closure_set(x_150, 1, x_145);
lean_closure_set(x_150, 2, x_143);
x_151 = l_Lake_EStateT_instFunctor___redArg(x_144);
x_152 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_152, 0, x_145);
lean_inc_ref(x_151);
if (lean_is_scalar(x_146)) {
 x_153 = lean_alloc_ctor(0, 5, 0);
} else {
 x_153 = x_146;
}
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
lean_ctor_set(x_153, 2, x_150);
lean_ctor_set(x_153, 3, x_149);
lean_ctor_set(x_153, 4, x_148);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_147);
lean_inc_ref(x_151);
x_155 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_155, 0, x_151);
x_156 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_156, 0, x_151);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
x_158 = l_Lake_instMonadWorkspaceJobM___closed__14;
lean_inc_ref(x_154);
x_159 = l_ReaderT_instAlternativeOfMonad___redArg(x_158, x_154);
x_160 = l_ReaderT_instMonad___redArg(x_154);
lean_inc_ref(x_160);
x_161 = l_ReaderT_instAlternativeOfMonad___redArg(x_159, x_160);
x_162 = lean_ctor_get(x_161, 0);
lean_inc_ref(x_162);
lean_dec_ref(x_161);
x_163 = lean_ctor_get(x_162, 0);
lean_inc_ref(x_163);
lean_dec_ref(x_162);
x_164 = l_ReaderT_instMonad___redArg(x_160);
x_165 = lean_ctor_get(x_164, 0);
lean_inc_ref(x_165);
x_166 = lean_ctor_get(x_165, 0);
lean_inc_ref(x_166);
lean_dec_ref(x_165);
lean_inc_ref(x_166);
x_167 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_167, 0, x_166);
x_168 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_168, 0, x_166);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
x_170 = l_ReaderT_instMonad___redArg(x_164);
x_171 = lean_ctor_get(x_170, 0);
lean_inc_ref(x_171);
x_172 = lean_ctor_get(x_171, 0);
lean_inc_ref(x_172);
lean_dec_ref(x_171);
lean_inc_ref(x_172);
x_173 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_173, 0, x_172);
x_174 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_174, 0, x_172);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
lean_inc_ref(x_175);
x_176 = l_Lake_EquipT_instFunctor___redArg(x_175);
x_177 = lean_ctor_get(x_170, 0);
lean_inc_ref(x_177);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_178 = x_170;
} else {
 lean_dec_ref(x_170);
 x_178 = lean_box(0);
}
x_179 = lean_ctor_get(x_177, 0);
lean_inc_ref(x_179);
lean_dec_ref(x_177);
x_180 = l_Lake_instMonadWorkspaceJobM___closed__20;
lean_inc_ref(x_157);
x_181 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_180, x_157);
x_182 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_181, x_157);
x_183 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(x_183, 0, lean_box(0));
lean_closure_set(x_183, 1, lean_box(0));
lean_closure_set(x_183, 2, lean_box(0));
lean_closure_set(x_183, 3, lean_box(0));
lean_closure_set(x_183, 4, x_182);
lean_inc_ref(x_163);
x_184 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_183, x_163);
x_185 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_184, x_163);
x_186 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_186, 0, lean_box(0));
lean_closure_set(x_186, 1, x_185);
lean_inc_ref(x_169);
x_187 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_186, x_169);
x_188 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_187, x_169);
x_189 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_189, 0, lean_box(0));
lean_closure_set(x_189, 1, x_188);
lean_inc_ref(x_175);
x_190 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_189, x_175);
x_191 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_190, x_175);
x_192 = lean_alloc_closure((void*)(l_Lake_EquipT_lift___boxed), 5, 4);
lean_closure_set(x_192, 0, lean_box(0));
lean_closure_set(x_192, 1, lean_box(0));
lean_closure_set(x_192, 2, lean_box(0));
lean_closure_set(x_192, 3, x_191);
lean_inc_ref(x_176);
x_193 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_192, x_176);
x_194 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_193, x_176);
x_195 = lean_alloc_closure((void*)(l_Lake_JobM_runFetchM___boxed), 9, 2);
lean_closure_set(x_195, 0, lean_box(0));
lean_closure_set(x_195, 1, x_194);
lean_inc_ref(x_179);
x_196 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_196, 0, x_179);
x_197 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_197, 0, x_179);
if (lean_is_scalar(x_178)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_178;
}
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
x_199 = l_Lake_EquipT_instFunctor___redArg(x_198);
x_200 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_195, x_199);
return x_200;
}
}
}
static lean_object* _init_l_Lake_platformTrace___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_System_Platform_target;
return x_1;
}
}
static uint64_t _init_l_Lake_platformTrace___closed__1() {
_start:
{
uint64_t x_1; 
x_1 = l_Lake_Hash_nil;
return x_1;
}
}
static uint64_t _init_l_Lake_platformTrace___closed__2() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = l_Lake_platformTrace___closed__0;
x_2 = lean_string_hash(x_1);
return x_2;
}
}
static uint64_t _init_l_Lake_platformTrace___closed__3() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = l_Lake_platformTrace___closed__2;
x_2 = l_Lake_platformTrace___closed__1;
x_3 = lean_uint64_mix_hash(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_platformTrace___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_platformTrace___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_platformTrace___closed__6() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lake_platformTrace___closed__5;
x_3 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_platformTrace___closed__7() {
_start:
{
lean_object* x_1; uint64_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_platformTrace___closed__6;
x_2 = l_Lake_platformTrace___closed__3;
x_3 = l_Lake_platformTrace___closed__4;
x_4 = l_Lake_platformTrace___closed__0;
x_5 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set_uint64(x_5, sizeof(void*)*3, x_2);
return x_5;
}
}
static lean_object* _init_l_Lake_platformTrace() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_platformTrace___closed__7;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___redArg(lean_object* x_1) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lake_platformTrace;
x_6 = lean_box(0);
x_7 = l_Lake_BuildTrace_mix(x_4, x_5);
lean_ctor_set(x_1, 1, x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_1);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_dec(x_1);
x_13 = l_Lake_platformTrace;
x_14 = lean_box(0);
x_15 = l_Lake_BuildTrace_mix(x_11, x_13);
x_16 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_12);
lean_ctor_set_uint8(x_16, sizeof(void*)*3, x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Lake_platformTrace;
x_11 = lean_box(0);
x_12 = l_Lake_BuildTrace_mix(x_9, x_10);
lean_ctor_set(x_6, 1, x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
x_16 = lean_ctor_get(x_6, 1);
x_17 = lean_ctor_get(x_6, 2);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_14);
lean_dec(x_6);
x_18 = l_Lake_platformTrace;
x_19 = lean_box(0);
x_20 = l_Lake_BuildTrace_mix(x_16, x_18);
x_21 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_17);
lean_ctor_set_uint8(x_21, sizeof(void*)*3, x_15);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_addPlatformTrace___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_addPlatformTrace(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_6);
lean_dec_ref(x_1);
x_7 = lean_box(0);
x_8 = l_Lake_BuildTrace_mix(x_5, x_6);
lean_ctor_set(x_2, 1, x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_14);
lean_dec_ref(x_1);
x_15 = lean_box(0);
x_16 = l_Lake_BuildTrace_mix(x_12, x_14);
x_17 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_13);
lean_ctor_set_uint8(x_17, sizeof(void*)*3, x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lake_addLeanTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_10);
lean_dec_ref(x_5);
x_11 = lean_box(0);
x_12 = l_Lake_BuildTrace_mix(x_9, x_10);
lean_ctor_set(x_6, 1, x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
x_16 = lean_ctor_get(x_6, 1);
x_17 = lean_ctor_get(x_6, 2);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_14);
lean_dec(x_6);
x_18 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_18);
lean_dec_ref(x_5);
x_19 = lean_box(0);
x_20 = l_Lake_BuildTrace_mix(x_16, x_18);
x_21 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_17);
lean_ctor_set_uint8(x_21, sizeof(void*)*3, x_15);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_addLeanTrace___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_addLeanTrace(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
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
LEAN_EXPORT lean_object* l_Lake_addPureTrace___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_3);
x_9 = lean_apply_1(x_2, x_3);
x_10 = l_Lake_addPureTrace___redArg___closed__0;
x_11 = lean_string_append(x_4, x_10);
x_12 = lean_apply_1(x_1, x_3);
x_13 = lean_string_append(x_11, x_12);
lean_dec_ref(x_12);
x_14 = l_Lake_platformTrace___closed__4;
x_15 = l_Lake_platformTrace___closed__6;
x_16 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_unbox_uint64(x_9);
lean_dec(x_9);
lean_ctor_set_uint64(x_16, sizeof(void*)*3, x_17);
x_18 = lean_box(0);
x_19 = l_Lake_BuildTrace_mix(x_8, x_16);
lean_ctor_set(x_5, 1, x_19);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_5);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint64_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_21 = lean_ctor_get(x_5, 0);
x_22 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
x_23 = lean_ctor_get(x_5, 1);
x_24 = lean_ctor_get(x_5, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_21);
lean_dec(x_5);
lean_inc(x_3);
x_25 = lean_apply_1(x_2, x_3);
x_26 = l_Lake_addPureTrace___redArg___closed__0;
x_27 = lean_string_append(x_4, x_26);
x_28 = lean_apply_1(x_1, x_3);
x_29 = lean_string_append(x_27, x_28);
lean_dec_ref(x_28);
x_30 = l_Lake_platformTrace___closed__4;
x_31 = l_Lake_platformTrace___closed__6;
x_32 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_31);
x_33 = lean_unbox_uint64(x_25);
lean_dec(x_25);
lean_ctor_set_uint64(x_32, sizeof(void*)*3, x_33);
x_34 = lean_box(0);
x_35 = l_Lake_BuildTrace_mix(x_23, x_32);
x_36 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_36, 0, x_21);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_24);
lean_ctor_set_uint8(x_36, sizeof(void*)*3, x_22);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lake_addPureTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_4);
x_15 = lean_apply_1(x_3, x_4);
x_16 = l_Lake_addPureTrace___redArg___closed__0;
x_17 = lean_string_append(x_5, x_16);
x_18 = lean_apply_1(x_2, x_4);
x_19 = lean_string_append(x_17, x_18);
lean_dec_ref(x_18);
x_20 = l_Lake_platformTrace___closed__4;
x_21 = l_Lake_platformTrace___closed__6;
x_22 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_unbox_uint64(x_15);
lean_dec(x_15);
lean_ctor_set_uint64(x_22, sizeof(void*)*3, x_23);
x_24 = lean_box(0);
x_25 = l_Lake_BuildTrace_mix(x_14, x_22);
lean_ctor_set(x_11, 1, x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_11);
return x_26;
}
else
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint64_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_27 = lean_ctor_get(x_11, 0);
x_28 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_29 = lean_ctor_get(x_11, 1);
x_30 = lean_ctor_get(x_11, 2);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_27);
lean_dec(x_11);
lean_inc(x_4);
x_31 = lean_apply_1(x_3, x_4);
x_32 = l_Lake_addPureTrace___redArg___closed__0;
x_33 = lean_string_append(x_5, x_32);
x_34 = lean_apply_1(x_2, x_4);
x_35 = lean_string_append(x_33, x_34);
lean_dec_ref(x_34);
x_36 = l_Lake_platformTrace___closed__4;
x_37 = l_Lake_platformTrace___closed__6;
x_38 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set(x_38, 2, x_37);
x_39 = lean_unbox_uint64(x_31);
lean_dec(x_31);
lean_ctor_set_uint64(x_38, sizeof(void*)*3, x_39);
x_40 = lean_box(0);
x_41 = l_Lake_BuildTrace_mix(x_29, x_38);
x_42 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_42, 0, x_27);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_42, 2, x_30);
lean_ctor_set_uint8(x_42, sizeof(void*)*3, x_28);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l_Lake_addPureTrace___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_addPureTrace___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_addPureTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_addPureTrace(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_BuildMetadata_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("2025-09-10", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0;
return x_1;
}
}
static lean_object* _init_l_Prod_toJson___at___Array_toJson___at___Lake_BuildMetadata_toJson_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Prod_toJson___at___Array_toJson___at___Lake_BuildMetadata_toJson_spec__0_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_2);
x_5 = l_Prod_toJson___at___Array_toJson___at___Lake_BuildMetadata_toJson_spec__0_spec__0___closed__0;
x_6 = lean_array_push(x_5, x_4);
x_7 = lean_array_push(x_6, x_3);
x_8 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_toJson___at___Lake_BuildMetadata_toJson_spec__0_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Prod_toJson___at___Array_toJson___at___Lake_BuildMetadata_toJson_spec__0_spec__0(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___Lake_BuildMetadata_toJson_spec__0(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_toJson___at___Lake_BuildMetadata_toJson_spec__0_spec__1(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___Lake_BuildMetadata_toJson_spec__3(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_toJson___at___Lake_BuildMetadata_toJson_spec__4_spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lake_instToJsonLogEntry_toJson(x_5);
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
LEAN_EXPORT lean_object* l_Array_toJson___at___Lake_BuildMetadata_toJson_spec__4(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_toJson___at___Lake_BuildMetadata_toJson_spec__4_spec__4(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_BuildMetadata_toJson___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("schemaVersion", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildMetadata_toJson___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_BuildMetadata_toJson___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_BuildMetadata_toJson___closed__1;
x_2 = l_Lake_BuildMetadata_toJson___closed__0;
x_3 = lean_box(1);
x_4 = l_Lake_JsonObject_insertJson(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_BuildMetadata_toJson___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("depHash", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildMetadata_toJson___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inputs", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildMetadata_toJson___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("outputs", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildMetadata_toJson___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("log", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildMetadata_toJson___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("synthetic", 9, 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_toJson(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_2 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_5);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec_ref(x_1);
x_7 = l_Lake_BuildMetadata_toJson___closed__2;
x_8 = l_Lake_BuildMetadata_toJson___closed__3;
x_9 = l_Lake_Hash_hex(x_2);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Lake_JsonObject_insertJson(x_7, x_8, x_10);
x_12 = l_Lake_BuildMetadata_toJson___closed__4;
x_13 = l_Array_toJson___at___Lake_BuildMetadata_toJson_spec__0(x_3);
x_14 = l_Lake_JsonObject_insertJson(x_11, x_12, x_13);
x_15 = l_Lake_BuildMetadata_toJson___closed__5;
x_16 = l_Option_toJson___at___Lake_BuildMetadata_toJson_spec__3(x_4);
lean_dec(x_4);
x_17 = l_Lake_JsonObject_insertJson(x_14, x_15, x_16);
x_18 = l_Lake_BuildMetadata_toJson___closed__6;
x_19 = l_Array_toJson___at___Lake_BuildMetadata_toJson_spec__4(x_5);
x_20 = l_Lake_JsonObject_insertJson(x_17, x_18, x_19);
x_21 = l_Lake_BuildMetadata_toJson___closed__7;
x_22 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_22, 0, x_6);
x_23 = l_Lake_JsonObject_insertJson(x_20, x_21, x_22);
x_24 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_toJson___at___Lake_BuildMetadata_toJson_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_toJson___at___Lake_BuildMetadata_toJson_spec__0_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___Lake_BuildMetadata_toJson_spec__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Option_toJson___at___Lake_BuildMetadata_toJson_spec__3(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_toJson___at___Lake_BuildMetadata_toJson_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_toJson___at___Lake_BuildMetadata_toJson_spec__4_spec__4(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lake_instToJsonBuildMetadata___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_BuildMetadata_toJson), 1, 0);
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
static lean_object* _init_l_Lake_BuildMetadata_ofStub___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofStub(uint64_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = l_Lake_BuildMetadata_ofStub___closed__0;
x_3 = lean_box(0);
x_4 = 0;
x_5 = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set_uint64(x_5, sizeof(void*)*3, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*3 + 8, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofStub___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lake_BuildMetadata_ofStub(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofHash(uint64_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_BuildMetadata_ofStub(x_1);
return x_2;
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
static lean_object* _init_l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__0___closed__0;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lean_Json_getBool_x3f(x_1);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_7 = l_Lake_instFromJsonLogEntry_fromJson(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec_ref(x_3);
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
lean_dec_ref(x_7);
x_12 = lean_unsigned_to_nat(0u);
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
static lean_object* _init_l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = lean_array_size(x_2);
x_4 = 0;
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__1(x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__0;
x_7 = lean_unsigned_to_nat(80u);
x_8 = l_Lean_Json_pretty(x_1, x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec_ref(x_8);
x_10 = l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
static lean_object* _init_l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__1___closed__0;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1(x_1);
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
static lean_object* _init_l_Option_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__4_spec__4___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__4_spec__4(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__4_spec__4___closed__0;
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
static lean_object* _init_l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__4___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__4(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__4___closed__0;
return x_2;
}
else
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Option_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__4_spec__4(x_1);
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
static lean_object* _init_l_Prod_fromJson_x3f___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__6_spec__6_spec__6___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected pair, got '", 20, 20);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__6_spec__6_spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
x_2 = x_1;
goto block_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc_ref(x_11);
lean_dec_ref(x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_fget_borrowed(x_11, x_15);
lean_inc(x_16);
x_17 = l_Lean_Json_getStr_x3f(x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec_ref(x_11);
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
lean_dec_ref(x_11);
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
lean_dec_ref(x_11);
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
x_3 = l_Prod_fromJson_x3f___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__6_spec__6_spec__6___closed__0;
x_4 = lean_unsigned_to_nat(80u);
x_5 = l_Lean_Json_pretty(x_2, x_4);
x_6 = lean_string_append(x_3, x_5);
lean_dec_ref(x_5);
x_7 = l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__6_spec__6_spec__7(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_7 = l_Prod_fromJson_x3f___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__6_spec__6_spec__6(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec_ref(x_3);
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
lean_dec_ref(x_7);
x_12 = lean_unsigned_to_nat(0u);
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
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__6_spec__6(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = lean_array_size(x_2);
x_4 = 0;
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__6_spec__6_spec__7(x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__0;
x_7 = lean_unsigned_to_nat(80u);
x_8 = l_Lean_Json_pretty(x_1, x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec_ref(x_8);
x_10 = l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
static lean_object* _init_l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__6___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__6(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__6___closed__0;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__6_spec__6(x_1);
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
static lean_object* _init_l_Lake_BuildMetadata_fromJsonObject_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("synthetic: ", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJsonObject_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("log: ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJsonObject_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("outputs: ", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJsonObject_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inputs: ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJsonObject_x3f___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("property not found: depHash", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJsonObject_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_BuildMetadata_fromJsonObject_x3f___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("depHash: ", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJsonObject_x3f___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid trace: expected string 'depHash' of decimal digits", 58, 58);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJsonObject_x3f___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_BuildMetadata_fromJsonObject_x3f___closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint64_t x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_10; uint64_t x_11; lean_object* x_12; lean_object* x_13; uint64_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint64_t x_39; lean_object* x_40; lean_object* x_41; uint64_t x_44; lean_object* x_45; lean_object* x_46; uint64_t x_65; lean_object* x_66; uint64_t x_69; lean_object* x_70; uint64_t x_78; uint64_t x_81; lean_object* x_100; lean_object* x_101; 
x_100 = l_Lake_BuildMetadata_toJson___closed__0;
x_101 = l_Lake_JsonObject_getJson_x3f(x_1, x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = l_Lake_BuildMetadata_toJson___closed__3;
x_103 = l_Lake_JsonObject_getJson_x3f(x_1, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; 
x_104 = l_Lake_BuildMetadata_fromJsonObject_x3f___closed__7;
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
lean_dec_ref(x_103);
x_106 = l_Lean_Json_getStr_x3f(x_105);
if (lean_obj_tag(x_106) == 0)
{
uint8_t x_107; 
x_107 = !lean_is_exclusive(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_106, 0);
x_109 = l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8;
x_110 = lean_string_append(x_109, x_108);
lean_dec(x_108);
lean_ctor_set(x_106, 0, x_110);
return x_106;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_ctor_get(x_106, 0);
lean_inc(x_111);
lean_dec(x_106);
x_112 = l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8;
x_113 = lean_string_append(x_112, x_111);
lean_dec(x_111);
x_114 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_114, 0, x_113);
return x_114;
}
}
else
{
if (lean_obj_tag(x_106) == 0)
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_106);
if (x_115 == 0)
{
lean_ctor_set_tag(x_106, 0);
return x_106;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_106, 0);
lean_inc(x_116);
lean_dec(x_106);
x_117 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_117, 0, x_116);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_106, 0);
lean_inc(x_118);
lean_dec_ref(x_106);
x_119 = l_Lake_Hash_ofDecimal_x3f(x_118);
lean_dec(x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; 
x_120 = l_Lake_BuildMetadata_fromJsonObject_x3f___closed__10;
return x_120;
}
else
{
lean_object* x_121; uint64_t x_122; 
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
lean_dec_ref(x_119);
x_122 = lean_unbox_uint64(x_121);
lean_dec(x_121);
x_81 = x_122;
goto block_99;
}
}
}
}
}
else
{
lean_object* x_123; lean_object* x_124; 
lean_dec_ref(x_101);
x_123 = l_Lake_BuildMetadata_toJson___closed__3;
x_124 = l_Lake_JsonObject_getJson_x3f(x_1, x_123);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; 
x_125 = l_Lake_BuildMetadata_fromJsonObject_x3f___closed__7;
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
lean_dec_ref(x_124);
x_127 = l_Lake_Hash_fromJson_x3f(x_126);
if (lean_obj_tag(x_127) == 0)
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_127, 0);
x_130 = l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8;
x_131 = lean_string_append(x_130, x_129);
lean_dec(x_129);
lean_ctor_set(x_127, 0, x_131);
return x_127;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_132 = lean_ctor_get(x_127, 0);
lean_inc(x_132);
lean_dec(x_127);
x_133 = l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8;
x_134 = lean_string_append(x_133, x_132);
lean_dec(x_132);
x_135 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_135, 0, x_134);
return x_135;
}
}
else
{
if (lean_obj_tag(x_127) == 0)
{
uint8_t x_136; 
x_136 = !lean_is_exclusive(x_127);
if (x_136 == 0)
{
lean_ctor_set_tag(x_127, 0);
return x_127;
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_127, 0);
lean_inc(x_137);
lean_dec(x_127);
x_138 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_138, 0, x_137);
return x_138;
}
}
else
{
lean_object* x_139; uint64_t x_140; 
x_139 = lean_ctor_get(x_127, 0);
lean_inc(x_139);
lean_dec_ref(x_127);
x_140 = lean_unbox_uint64(x_139);
lean_dec(x_139);
x_81 = x_140;
goto block_99;
}
}
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_2);
lean_ctor_set_uint64(x_7, sizeof(void*)*3, x_3);
lean_ctor_set_uint8(x_7, sizeof(void*)*3 + 8, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
block_15:
{
uint8_t x_14; 
x_14 = 0;
x_2 = x_10;
x_3 = x_11;
x_4 = x_12;
x_5 = x_13;
x_6 = x_14;
goto block_9;
}
block_38:
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Lake_BuildMetadata_toJson___closed__7;
x_21 = l_Lake_JsonObject_getJson_x3f(x_1, x_20);
if (lean_obj_tag(x_21) == 0)
{
x_10 = x_19;
x_11 = x_16;
x_12 = x_17;
x_13 = x_18;
goto block_15;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__0(x_22);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = l_Lake_BuildMetadata_fromJsonObject_x3f___closed__0;
x_27 = lean_string_append(x_26, x_25);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_27);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
lean_dec(x_23);
x_29 = l_Lake_BuildMetadata_fromJsonObject_x3f___closed__0;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
else
{
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_32; 
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
lean_ctor_set_tag(x_23, 0);
return x_23;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_23, 0);
lean_inc(x_33);
lean_dec(x_23);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
else
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_23, 0);
lean_inc(x_35);
lean_dec_ref(x_23);
if (lean_obj_tag(x_35) == 0)
{
x_10 = x_19;
x_11 = x_16;
x_12 = x_17;
x_13 = x_18;
goto block_15;
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
x_2 = x_19;
x_3 = x_16;
x_4 = x_17;
x_5 = x_18;
x_6 = x_37;
goto block_9;
}
}
}
}
}
block_43:
{
lean_object* x_42; 
x_42 = l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1;
x_16 = x_39;
x_17 = x_40;
x_18 = x_41;
x_19 = x_42;
goto block_38;
}
block_64:
{
lean_object* x_47; lean_object* x_48; 
x_47 = l_Lake_BuildMetadata_toJson___closed__6;
x_48 = l_Lake_JsonObject_getJson_x3f(x_1, x_47);
if (lean_obj_tag(x_48) == 0)
{
x_39 = x_44;
x_40 = x_46;
x_41 = x_45;
goto block_43;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
x_50 = l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__1(x_49);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
lean_dec(x_46);
lean_dec_ref(x_45);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = l_Lake_BuildMetadata_fromJsonObject_x3f___closed__2;
x_54 = lean_string_append(x_53, x_52);
lean_dec(x_52);
lean_ctor_set(x_50, 0, x_54);
return x_50;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_50, 0);
lean_inc(x_55);
lean_dec(x_50);
x_56 = l_Lake_BuildMetadata_fromJsonObject_x3f___closed__2;
x_57 = lean_string_append(x_56, x_55);
lean_dec(x_55);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
else
{
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_59; 
lean_dec(x_46);
lean_dec_ref(x_45);
x_59 = !lean_is_exclusive(x_50);
if (x_59 == 0)
{
lean_ctor_set_tag(x_50, 0);
return x_50;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_50, 0);
lean_inc(x_60);
lean_dec(x_50);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
else
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_50, 0);
lean_inc(x_62);
lean_dec_ref(x_50);
if (lean_obj_tag(x_62) == 0)
{
x_39 = x_44;
x_40 = x_46;
x_41 = x_45;
goto block_43;
}
else
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_16 = x_44;
x_17 = x_46;
x_18 = x_45;
x_19 = x_63;
goto block_38;
}
}
}
}
}
block_68:
{
lean_object* x_67; 
x_67 = lean_box(0);
x_44 = x_65;
x_45 = x_66;
x_46 = x_67;
goto block_64;
}
block_77:
{
lean_object* x_71; lean_object* x_72; 
x_71 = l_Lake_BuildMetadata_toJson___closed__5;
x_72 = l_Lake_JsonObject_getJson_x3f(x_1, x_71);
if (lean_obj_tag(x_72) == 0)
{
x_65 = x_69;
x_66 = x_70;
goto block_68;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec_ref(x_72);
x_74 = l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__4(x_73);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec_ref(x_74);
if (lean_obj_tag(x_75) == 0)
{
x_65 = x_69;
x_66 = x_70;
goto block_68;
}
else
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec_ref(x_75);
x_44 = x_69;
x_45 = x_70;
x_46 = x_76;
goto block_64;
}
}
}
block_80:
{
lean_object* x_79; 
x_79 = l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4;
x_69 = x_78;
x_70 = x_79;
goto block_77;
}
block_99:
{
lean_object* x_82; lean_object* x_83; 
x_82 = l_Lake_BuildMetadata_toJson___closed__4;
x_83 = l_Lake_JsonObject_getJson_x3f(x_1, x_82);
if (lean_obj_tag(x_83) == 0)
{
x_78 = x_81;
goto block_80;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
x_85 = l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__6(x_84);
if (lean_obj_tag(x_85) == 0)
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_85, 0);
x_88 = l_Lake_BuildMetadata_fromJsonObject_x3f___closed__5;
x_89 = lean_string_append(x_88, x_87);
lean_dec(x_87);
lean_ctor_set(x_85, 0, x_89);
return x_85;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_85, 0);
lean_inc(x_90);
lean_dec(x_85);
x_91 = l_Lake_BuildMetadata_fromJsonObject_x3f___closed__5;
x_92 = lean_string_append(x_91, x_90);
lean_dec(x_90);
x_93 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
}
else
{
if (lean_obj_tag(x_85) == 0)
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_85);
if (x_94 == 0)
{
lean_ctor_set_tag(x_85, 0);
return x_85;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_85, 0);
lean_inc(x_95);
lean_dec(x_85);
x_96 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_96, 0, x_95);
return x_96;
}
}
else
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_85, 0);
lean_inc(x_97);
lean_dec_ref(x_85);
if (lean_obj_tag(x_97) == 0)
{
x_78 = x_81;
goto block_80;
}
else
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec_ref(x_97);
x_69 = x_81;
x_70 = x_98;
goto block_77;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__6_spec__6_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__6_spec__6_spec__7(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_BuildMetadata_fromJsonObject_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown trace format: ", 22, 22);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJson_x3f___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lake_BuildMetadata_fromJson_x3f___lam__0___closed__0;
x_4 = lean_string_append(x_3, x_1);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid trace stub: ", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid trace: ", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown trace format: expected JSON number or object", 52, 52);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_BuildMetadata_fromJson_x3f___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJson_x3f(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Lake_Hash_ofJsonNumber_x3f(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lake_BuildMetadata_fromJson_x3f___closed__0;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = l_Lake_BuildMetadata_fromJson_x3f___closed__0;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; uint64_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_unbox_uint64(x_13);
lean_dec(x_13);
x_15 = l_Lake_BuildMetadata_ofStub(x_14);
lean_ctor_set(x_3, 0, x_15);
return x_3;
}
else
{
lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_unbox_uint64(x_16);
lean_dec(x_16);
x_18 = l_Lake_BuildMetadata_ofStub(x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
case 5:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = l_Lake_BuildMetadata_fromJsonObject_x3f(x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_21, 0);
x_27 = l_Lake_BuildMetadata_toJson___closed__0;
x_28 = l_Lake_JsonObject_getJson_x3f(x_20, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_free_object(x_21);
goto block_26;
}
else
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
if (lean_obj_tag(x_29) == 3)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc_ref(x_30);
lean_dec_ref(x_29);
x_31 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0;
x_32 = lean_string_dec_eq(x_30, x_31);
lean_dec_ref(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_free_object(x_21);
x_33 = lean_box(0);
x_34 = l_Lake_BuildMetadata_fromJson_x3f___lam__0(x_23, x_33);
lean_dec(x_23);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Lake_BuildMetadata_fromJson_x3f___closed__1;
x_36 = lean_string_append(x_35, x_23);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_36);
return x_21;
}
}
else
{
lean_dec(x_29);
lean_free_object(x_21);
goto block_26;
}
}
block_26:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = l_Lake_BuildMetadata_fromJson_x3f___lam__0(x_23, x_24);
lean_dec(x_23);
return x_25;
}
}
else
{
lean_object* x_37; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_21, 0);
lean_inc(x_37);
lean_dec(x_21);
x_41 = l_Lake_BuildMetadata_toJson___closed__0;
x_42 = l_Lake_JsonObject_getJson_x3f(x_20, x_41);
if (lean_obj_tag(x_42) == 0)
{
goto block_40;
}
else
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
if (lean_obj_tag(x_43) == 3)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc_ref(x_44);
lean_dec_ref(x_43);
x_45 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0;
x_46 = lean_string_dec_eq(x_44, x_45);
lean_dec_ref(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_box(0);
x_48 = l_Lake_BuildMetadata_fromJson_x3f___lam__0(x_37, x_47);
lean_dec(x_37);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = l_Lake_BuildMetadata_fromJson_x3f___closed__1;
x_50 = lean_string_append(x_49, x_37);
lean_dec(x_37);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
else
{
lean_dec(x_43);
goto block_40;
}
}
block_40:
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_box(0);
x_39 = l_Lake_BuildMetadata_fromJson_x3f___lam__0(x_37, x_38);
lean_dec(x_37);
return x_39;
}
}
}
else
{
return x_21;
}
}
default: 
{
lean_object* x_52; 
x_52 = l_Lake_BuildMetadata_fromJson_x3f___closed__3;
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJson_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_BuildMetadata_fromJson_x3f___lam__0(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJson_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_BuildMetadata_fromJson_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instFromJsonBuildMetadata___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_BuildMetadata_fromJson_x3f___boxed), 1, 0);
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
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_parse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_parse(x_1);
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
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = l_Lake_BuildMetadata_fromJson_x3f(x_6);
lean_dec(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofFetch(uint64_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_3 = l_Lake_BuildMetadata_ofStub___closed__0;
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_2);
x_5 = 1;
x_6 = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set_uint64(x_6, sizeof(void*)*3, x_1);
lean_ctor_set_uint8(x_6, sizeof(void*)*3 + 8, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofFetch___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Lake_BuildMetadata_ofFetch(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_serializeInputs_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_15; uint64_t x_16; uint8_t x_17; 
x_6 = lean_array_uget(x_1, x_2);
x_15 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_15);
x_16 = lean_ctor_get_uint64(x_6, sizeof(void*)*3);
x_17 = l_Array_isEmpty___redArg(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = l___private_Lake_Build_Common_0__Lake_serializeInputs(x_15);
lean_dec_ref(x_15);
x_19 = l_Array_toJson___at___Lake_BuildMetadata_toJson_spec__0(x_18);
x_7 = x_19;
goto block_14;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_15);
x_20 = l_Lake_Hash_hex(x_16);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_7 = x_21;
goto block_14;
}
block_14:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_6);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_15; uint64_t x_16; uint8_t x_17; 
x_6 = lean_array_uget(x_1, x_2);
x_15 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_15);
x_16 = lean_ctor_get_uint64(x_6, sizeof(void*)*3);
x_17 = l_Array_isEmpty___redArg(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = l___private_Lake_Build_Common_0__Lake_serializeInputs(x_15);
lean_dec_ref(x_15);
x_19 = l_Array_toJson___at___Lake_BuildMetadata_toJson_spec__0(x_18);
x_7 = x_19;
goto block_14;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_15);
x_20 = l_Lake_Hash_hex(x_16);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_7 = x_21;
goto block_14;
}
block_14:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_array_push(x_4, x_9);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_serializeInputs_spec__0_spec__0(x_1, x_12, x_3, x_10);
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
x_2 = l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4;
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
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(x_1, x_7, x_8, x_2);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_serializeInputs_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_serializeInputs_spec__0_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_serializeInputs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_serializeInputs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Build_Common_0__Lake_serializeInputs(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_6 = l___private_Lake_Build_Common_0__Lake_serializeInputs(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_2);
x_8 = 0;
x_9 = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_3);
lean_ctor_set_uint64(x_9, sizeof(void*)*3, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*3 + 8, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_apply_1(x_1, x_3);
x_6 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_apply_1(x_2, x_4);
x_7 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_BuildMetadata_ofBuild___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_BuildMetadata_ofBuild(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorIdx(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_SavedTrace_ctorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_SavedTrace_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_SavedTrace_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_missing_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_SavedTrace_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_missing_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_SavedTrace_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_invalid_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_SavedTrace_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_invalid_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_SavedTrace_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ok_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_SavedTrace_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ok_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_SavedTrace_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_readTraceFile___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": read failed: ", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_readTraceFile(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_readFile(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_16; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_16 = l_Lean_Json_parse(x_5);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_6 = x_17;
goto block_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = l_Lake_BuildMetadata_fromJson_x3f(x_18);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_6 = x_20;
goto block_15;
}
else
{
uint8_t x_21; 
lean_dec_ref(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; 
lean_ctor_set_tag(x_19, 2);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_2);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_2);
return x_25;
}
}
}
block_15:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = l_Lake_addPureTrace___redArg___closed__0;
x_8 = lean_string_append(x_1, x_7);
x_9 = lean_string_append(x_8, x_6);
lean_dec_ref(x_6);
x_10 = 2;
x_11 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_10);
x_12 = lean_array_push(x_2, x_11);
x_13 = lean_box(1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_4, 0);
lean_inc(x_26);
lean_dec_ref(x_4);
if (lean_obj_tag(x_26) == 11)
{
lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_26);
lean_dec_ref(x_1);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_2);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = l_Lake_readTraceFile___closed__0;
x_30 = lean_string_append(x_1, x_29);
x_31 = lean_io_error_to_string(x_26);
x_32 = lean_string_append(x_30, x_31);
lean_dec_ref(x_31);
x_33 = 3;
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_33);
x_35 = lean_array_get_size(x_2);
x_36 = lean_array_push(x_2, x_34);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_readTraceFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_readTraceFile(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_readTraceFile_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_readTraceFile(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 2)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_ctor_set_tag(x_5, 1);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_12);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_13 = x_5;
} else {
 lean_dec_ref(x_5);
 x_13 = lean_box(0);
}
if (lean_is_scalar(x_13)) {
 x_14 = lean_alloc_ctor(1, 1, 0);
} else {
 x_14 = x_13;
 lean_ctor_set_tag(x_14, 1);
}
lean_ctor_set(x_14, 0, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_5);
x_16 = !lean_is_exclusive(x_4);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_ctor_get(x_4, 0);
lean_dec(x_18);
x_19 = lean_array_get_size(x_17);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_19);
return x_4;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_4, 1);
lean_inc(x_20);
lean_dec(x_4);
x_21 = lean_array_get_size(x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
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
return x_4;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_4, 0);
x_25 = lean_ctor_get(x_4, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_4);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_readTraceFile_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_readTraceFile_x3f(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_writeFile(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_createParentDirs(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_4);
x_5 = l_Lake_BuildMetadata_toJson(x_2);
x_6 = lean_unsigned_to_nat(80u);
x_7 = l_Lean_Json_pretty(x_5, x_6);
x_8 = l_IO_FS_writeFile(x_1, x_7);
lean_dec_ref(x_7);
return x_8;
}
else
{
lean_dec_ref(x_2);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_writeFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_BuildMetadata_writeFile(x_1, x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_writeFetchTrace(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lake_BuildMetadata_ofFetch(x_2, x_3);
x_6 = l_Lake_BuildMetadata_writeFile(x_1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_writeFetchTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_6 = l_Lake_writeFetchTrace(x_1, x_5, x_3);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_apply_1(x_1, x_4);
x_8 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_3, x_7, x_5);
x_9 = l_Lake_BuildMetadata_writeFile(x_2, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_apply_1(x_2, x_5);
x_9 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_4, x_8, x_6);
x_10 = l_Lake_BuildMetadata_writeFile(x_3, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_writeBuildTrace___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_writeBuildTrace(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_writeTraceFile___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_apply_1(x_1, x_4);
x_8 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_3, x_7, x_5);
x_9 = l_Lake_BuildMetadata_writeFile(x_2, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_writeTraceFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_apply_1(x_2, x_5);
x_9 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_4, x_8, x_6);
x_10 = l_Lake_BuildMetadata_writeFile(x_3, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_writeTraceFile___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_writeTraceFile___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_writeTraceFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_writeTraceFile(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lake_OutputStatus_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OutputStatus_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lake_OutputStatus_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OutputStatus_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Lake_OutputStatus_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OutputStatus_outOfDate_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lake_OutputStatus_outOfDate_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OutputStatus_mtimeUpToDate_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lake_OutputStatus_mtimeUpToDate_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OutputStatus_hashUpToDate_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lake_OutputStatus_hashUpToDate_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_3 = l_Lake_OutputStatus_ctorIdx(x_1);
x_4 = l_Lake_OutputStatus_ctorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_alloc_closure((void*)(l_Lake_OutputStatus_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_OutputStatus_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OutputStatus_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Lake_OutputStatus_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
x_6 = lean_unbox(x_3);
x_7 = l_Lake_OutputStatus_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_le(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_dec_le(x_1, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 2;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_OutputStatus_ofNat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqOutputStatus(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lake_OutputStatus_ctorIdx(x_1);
x_4 = l_Lake_OutputStatus_ctorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqOutputStatus___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Lake_instDecidableEqOutputStatus(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofHashCheck(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 2;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofHashCheck___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Lake_OutputStatus_ofHashCheck(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofMTimeCheck(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofMTimeCheck___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Lake_OutputStatus_ofMTimeCheck(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_isUpToDate(uint8_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; 
x_2 = 0;
x_3 = l_Lake_instDecidableEqOutputStatus(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_isUpToDate___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Lake_OutputStatus_isUpToDate(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lake_OutputStatus_isCacheable(uint8_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; 
x_2 = 1;
x_3 = l_Lake_instDecidableEqOutputStatus(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_isCacheable___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Lake_OutputStatus_isCacheable(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lake_instDecidableEqHash___boxed), 2, 0);
x_2 = l_instBEqOfDecidableEq___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint64_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_11 = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0;
x_12 = lean_box_uint64(x_10);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Option_instBEq_beq___redArg(x_11, x_13, x_5);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
lean_dec_ref(x_1);
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
if (x_16 == 0)
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_17 = 0;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_8);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = l_Lake_MTime_checkUpToDate___redArg(x_2, x_3, x_6);
if (x_20 == 0)
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_21 = 0;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_8);
return x_23;
}
else
{
uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_24 = 1;
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_8);
return x_26;
}
}
}
else
{
lean_object* x_27; uint8_t x_28; 
lean_dec_ref(x_2);
x_27 = lean_apply_2(x_1, x_3, lean_box(0));
x_28 = lean_unbox(x_27);
if (x_28 == 0)
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_29 = 0;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_8);
return x_31;
}
else
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_32 = 2;
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_8);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = 0;
x_14 = lean_unbox(x_12);
lean_dec(x_12);
x_15 = l_Lake_instDecidableEqOutputStatus(x_14, x_13);
if (x_15 == 0)
{
uint8_t x_16; lean_object* x_17; 
x_16 = 1;
x_17 = lean_box(x_16);
lean_ctor_set(x_10, 0, x_17);
return x_10;
}
else
{
uint8_t x_18; lean_object* x_19; 
x_18 = 0;
x_19 = lean_box(x_18);
lean_ctor_set(x_10, 0, x_19);
return x_10;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_10);
x_22 = 0;
x_23 = lean_unbox(x_20);
lean_dec(x_20);
x_24 = l_Lake_instDecidableEqOutputStatus(x_23, x_22);
if (x_24 == 0)
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_25 = 1;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
else
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_28 = 0;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_21);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_12, x_13);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = 0;
x_19 = lean_unbox(x_17);
lean_dec(x_17);
x_20 = l_Lake_instDecidableEqOutputStatus(x_19, x_18);
if (x_20 == 0)
{
uint8_t x_21; lean_object* x_22; 
x_21 = 1;
x_22 = lean_box(x_21);
lean_ctor_set(x_15, 0, x_22);
return x_15;
}
else
{
uint8_t x_23; lean_object* x_24; 
x_23 = 0;
x_24 = lean_box(x_23);
lean_ctor_set(x_15, 0, x_24);
return x_15;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = 0;
x_28 = lean_unbox(x_25);
lean_dec(x_25);
x_29 = l_Lake_instDecidableEqOutputStatus(x_28, x_27);
if (x_29 == 0)
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_30 = 1;
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_26);
return x_32;
}
else
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_33 = 0;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_26);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_checkHashUpToDate___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lake_checkHashUpToDate(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_4);
lean_ctor_set(x_27, 1, x_5);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(x_1, x_2, x_3, x_4, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_get_size(x_1);
x_11 = lean_box(0);
x_12 = lean_nat_dec_lt(x_9, x_10);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_10, x_10);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(x_1, x_16, x_17, x_11, x_7);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(x_1, x_7, x_8, x_4, x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_5) == 2)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; uint64_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_27; uint8_t x_28; uint8_t x_29; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get_uint64(x_15, sizeof(void*)*3);
x_17 = lean_ctor_get(x_15, 2);
lean_inc_ref(x_17);
lean_dec_ref(x_15);
x_18 = lean_box_uint64(x_16);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_18);
x_19 = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_12);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_22 = x_19;
} else {
 lean_dec_ref(x_19);
 x_22 = lean_box(0);
}
x_27 = 0;
x_28 = lean_unbox(x_20);
x_29 = l_Lake_instDecidableEqOutputStatus(x_28, x_27);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
uint8_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get_uint8(x_21, sizeof(void*)*3);
x_32 = 1;
x_33 = l_Lake_JobAction_merge(x_31, x_32);
lean_ctor_set_uint8(x_21, sizeof(void*)*3, x_33);
x_34 = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(x_17, x_7, x_8, x_9, x_10, x_11, x_21);
lean_dec_ref(x_17);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec_ref(x_34);
x_23 = x_35;
x_24 = lean_box(0);
goto block_26;
}
else
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get_uint8(x_21, sizeof(void*)*3);
x_38 = lean_ctor_get(x_21, 1);
x_39 = lean_ctor_get(x_21, 2);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_36);
lean_dec(x_21);
x_40 = 1;
x_41 = l_Lake_JobAction_merge(x_37, x_40);
x_42 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_38);
lean_ctor_set(x_42, 2, x_39);
lean_ctor_set_uint8(x_42, sizeof(void*)*3, x_41);
x_43 = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(x_17, x_7, x_8, x_9, x_10, x_11, x_42);
lean_dec_ref(x_17);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec_ref(x_43);
x_23 = x_44;
x_24 = lean_box(0);
goto block_26;
}
}
else
{
lean_dec_ref(x_17);
x_23 = x_21;
x_24 = lean_box(0);
goto block_26;
}
block_26:
{
lean_object* x_25; 
if (lean_is_scalar(x_22)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_22;
}
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_45; uint64_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_58; uint8_t x_59; uint8_t x_60; 
x_45 = lean_ctor_get(x_5, 0);
lean_inc(x_45);
lean_dec(x_5);
x_46 = lean_ctor_get_uint64(x_45, sizeof(void*)*3);
x_47 = lean_ctor_get(x_45, 2);
lean_inc_ref(x_47);
lean_dec_ref(x_45);
x_48 = lean_box_uint64(x_46);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(x_1, x_2, x_3, x_4, x_49, x_6, x_11, x_12);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
x_58 = 0;
x_59 = lean_unbox(x_51);
x_60 = l_Lake_instDecidableEqOutputStatus(x_59, x_58);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_61 = lean_ctor_get(x_52, 0);
lean_inc_ref(x_61);
x_62 = lean_ctor_get_uint8(x_52, sizeof(void*)*3);
x_63 = lean_ctor_get(x_52, 1);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_52, 2);
lean_inc(x_64);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 x_65 = x_52;
} else {
 lean_dec_ref(x_52);
 x_65 = lean_box(0);
}
x_66 = 1;
x_67 = l_Lake_JobAction_merge(x_62, x_66);
if (lean_is_scalar(x_65)) {
 x_68 = lean_alloc_ctor(0, 3, 1);
} else {
 x_68 = x_65;
}
lean_ctor_set(x_68, 0, x_61);
lean_ctor_set(x_68, 1, x_63);
lean_ctor_set(x_68, 2, x_64);
lean_ctor_set_uint8(x_68, sizeof(void*)*3, x_67);
x_69 = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(x_47, x_7, x_8, x_9, x_10, x_11, x_68);
lean_dec_ref(x_47);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec_ref(x_69);
x_54 = x_70;
x_55 = lean_box(0);
goto block_57;
}
else
{
lean_dec_ref(x_47);
x_54 = x_52;
x_55 = lean_box(0);
goto block_57;
}
block_57:
{
lean_object* x_56; 
if (lean_is_scalar(x_53)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_53;
}
lean_ctor_set(x_56, 0, x_51);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
else
{
lean_object* x_71; uint8_t x_72; 
lean_dec(x_5);
lean_dec_ref(x_1);
x_71 = lean_ctor_get(x_11, 0);
x_72 = lean_ctor_get_uint8(x_71, sizeof(void*)*2);
if (x_72 == 0)
{
uint8_t x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_73 = 0;
x_74 = lean_box(x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_12);
return x_75;
}
else
{
uint8_t x_76; 
x_76 = l_Lake_MTime_checkUpToDate___redArg(x_2, x_3, x_6);
if (x_76 == 0)
{
uint8_t x_77; lean_object* x_78; lean_object* x_79; 
x_77 = 0;
x_78 = lean_box(x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_12);
return x_79;
}
else
{
uint8_t x_80; lean_object* x_81; lean_object* x_82; 
x_80 = 1;
x_81 = lean_box(x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_12);
return x_82;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lake_SavedTrace_replayIfUpToDate_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = 0;
x_18 = lean_unbox(x_16);
lean_dec(x_16);
x_19 = l_Lake_instDecidableEqOutputStatus(x_18, x_17);
if (x_19 == 0)
{
uint8_t x_20; lean_object* x_21; 
x_20 = 1;
x_21 = lean_box(x_20);
lean_ctor_set(x_14, 0, x_21);
return x_14;
}
else
{
uint8_t x_22; lean_object* x_23; 
x_22 = 0;
x_23 = lean_box(x_22);
lean_ctor_set(x_14, 0, x_23);
return x_14;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_14);
x_26 = 0;
x_27 = lean_unbox(x_24);
lean_dec(x_24);
x_28 = l_Lake_instDecidableEqOutputStatus(x_27, x_26);
if (x_28 == 0)
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_29 = 1;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_25);
return x_31;
}
else
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_32 = 0;
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_25);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = 0;
x_19 = lean_unbox(x_17);
lean_dec(x_17);
x_20 = l_Lake_instDecidableEqOutputStatus(x_19, x_18);
if (x_20 == 0)
{
uint8_t x_21; lean_object* x_22; 
x_21 = 1;
x_22 = lean_box(x_21);
lean_ctor_set(x_15, 0, x_22);
return x_15;
}
else
{
uint8_t x_23; lean_object* x_24; 
x_23 = 0;
x_24 = lean_box(x_23);
lean_ctor_set(x_15, 0, x_24);
return x_15;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = 0;
x_28 = lean_unbox(x_25);
lean_dec(x_25);
x_29 = l_Lake_instDecidableEqOutputStatus(x_28, x_27);
if (x_29 == 0)
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_30 = 1;
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_26);
return x_32;
}
else
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_33 = 0;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_26);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lake_SavedTrace_replayIfUpToDate___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lake_SavedTrace_replayIfUpToDate(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(uint64_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_25; uint64_t x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get_uint64(x_25, sizeof(void*)*3);
x_27 = lean_ctor_get(x_25, 2);
x_28 = lean_ctor_get_uint8(x_25, sizeof(void*)*3 + 8);
x_29 = lean_uint64_dec_eq(x_26, x_1);
if (x_29 == 0)
{
x_5 = x_3;
x_6 = lean_box(0);
goto block_24;
}
else
{
if (x_28 == 0)
{
goto block_64;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_array_get_size(x_27);
x_66 = lean_unsigned_to_nat(0u);
x_67 = lean_nat_dec_eq(x_65, x_66);
lean_dec(x_65);
if (x_67 == 0)
{
goto block_64;
}
else
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_3);
if (x_68 == 0)
{
uint8_t x_69; uint8_t x_70; uint8_t x_71; 
x_69 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_70 = 2;
x_71 = l_Lake_JobAction_merge(x_69, x_70);
lean_ctor_set_uint8(x_3, sizeof(void*)*3, x_71);
x_30 = x_3;
x_31 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_77; lean_object* x_78; 
x_72 = lean_ctor_get(x_3, 0);
x_73 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_74 = lean_ctor_get(x_3, 1);
x_75 = lean_ctor_get(x_3, 2);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_72);
lean_dec(x_3);
x_76 = 2;
x_77 = l_Lake_JobAction_merge(x_73, x_76);
x_78 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_78, 0, x_72);
lean_ctor_set(x_78, 1, x_74);
lean_ctor_set(x_78, 2, x_75);
lean_ctor_set_uint8(x_78, sizeof(void*)*3, x_77);
x_30 = x_78;
x_31 = lean_box(0);
goto block_34;
}
}
}
}
block_34:
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_box(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
block_64:
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_3);
if (x_35 == 0)
{
uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_36 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_37 = 1;
x_38 = l_Lake_JobAction_merge(x_36, x_37);
lean_ctor_set_uint8(x_3, sizeof(void*)*3, x_38);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_array_get_size(x_27);
x_41 = lean_nat_dec_lt(x_39, x_40);
if (x_41 == 0)
{
lean_dec(x_40);
x_30 = x_3;
x_31 = lean_box(0);
goto block_34;
}
else
{
uint8_t x_42; 
x_42 = lean_nat_dec_le(x_40, x_40);
if (x_42 == 0)
{
lean_dec(x_40);
x_30 = x_3;
x_31 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_43; size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_box(0);
x_44 = 0;
x_45 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_46 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(x_27, x_44, x_45, x_43, x_3);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec_ref(x_46);
x_30 = x_47;
x_31 = lean_box(0);
goto block_34;
}
}
}
else
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_48 = lean_ctor_get(x_3, 0);
x_49 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_50 = lean_ctor_get(x_3, 1);
x_51 = lean_ctor_get(x_3, 2);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_48);
lean_dec(x_3);
x_52 = 1;
x_53 = l_Lake_JobAction_merge(x_49, x_52);
x_54 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_50);
lean_ctor_set(x_54, 2, x_51);
lean_ctor_set_uint8(x_54, sizeof(void*)*3, x_53);
x_55 = lean_unsigned_to_nat(0u);
x_56 = lean_array_get_size(x_27);
x_57 = lean_nat_dec_lt(x_55, x_56);
if (x_57 == 0)
{
lean_dec(x_56);
x_30 = x_54;
x_31 = lean_box(0);
goto block_34;
}
else
{
uint8_t x_58; 
x_58 = lean_nat_dec_le(x_56, x_56);
if (x_58 == 0)
{
lean_dec(x_56);
x_30 = x_54;
x_31 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_59; size_t x_60; size_t x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_box(0);
x_60 = 0;
x_61 = lean_usize_of_nat(x_56);
lean_dec(x_56);
x_62 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(x_27, x_60, x_61, x_59, x_54);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec_ref(x_62);
x_30 = x_63;
x_31 = lean_box(0);
goto block_34;
}
}
}
}
}
else
{
x_5 = x_3;
x_6 = lean_box(0);
goto block_24;
}
block_24:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
x_9 = 2;
x_10 = l_Lake_JobAction_merge(x_8, x_9);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_10);
x_11 = 0;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_5, 2);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_14);
lean_dec(x_5);
x_18 = 2;
x_19 = l_Lake_JobAction_merge(x_15, x_18);
x_20 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*3, x_19);
x_21 = 0;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate(uint64_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(x_1, x_2, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_6 = l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(x_5, x_2, x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint64_t x_10; lean_object* x_11; 
x_10 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_11 = l_Lake_SavedTrace_replayOrFetchIfUpToDate(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_ToOutputJson_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ToOutputJson_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_ToOutputJson_ctorIdx(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonPUnit___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Lake_instToOutputJsonPUnit() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instToOutputJsonPUnit___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instToOutputJsonArtifact___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonArtifact___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint64_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get_uint64(x_2, sizeof(void*)*1);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_string_utf8_byte_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lake_Hash_hex(x_3);
x_9 = l_Lake_instToOutputJsonArtifact___lam__0___closed__0;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_string_append(x_10, x_4);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lake_Hash_hex(x_3);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
static lean_object* _init_l_Lake_instToOutputJsonArtifact() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instToOutputJsonArtifact___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonArtifact___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instToOutputJsonArtifact___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_io_mono_ms_now();
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_nat_sub(x_5, x_1);
lean_dec(x_5);
x_9 = lean_box(0);
x_10 = lean_nat_add(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
lean_ctor_set(x_3, 2, x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_12);
lean_dec(x_3);
x_16 = lean_nat_sub(x_5, x_1);
lean_dec(x_5);
x_17 = lean_box(0);
x_18 = lean_nat_add(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*3, x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
static lean_object* _init_l_Lake_buildAction___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("target is out-of-date and needs to be rebuilt", 45, 45);
return x_1;
}
}
static lean_object* _init_l_Lake_buildAction___redArg___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lake_buildAction___redArg___closed__0;
x_2 = 3;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get_uint8(x_18, sizeof(void*)*2 + 2);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_23 = lean_io_mono_ms_now();
x_24 = l_Lake_JobAction_merge(x_22, x_5);
lean_inc_ref(x_21);
lean_ctor_set_uint8(x_11, sizeof(void*)*3, x_24);
x_25 = lean_apply_7(x_4, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_25);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_34 = lean_ctor_get(x_25, 1);
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get_uint8(x_34, sizeof(void*)*3);
x_38 = lean_ctor_get(x_34, 1);
x_39 = lean_ctor_get(x_34, 2);
x_40 = lean_array_get_size(x_21);
lean_dec_ref(x_21);
x_41 = lean_array_get_size(x_36);
lean_inc(x_41);
x_42 = l_Array_extract___redArg(x_36, x_40, x_41);
lean_inc(x_35);
x_43 = lean_apply_1(x_1, x_35);
x_44 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_2, x_43, x_42);
x_45 = l_Lake_BuildMetadata_writeFile(x_3, x_44);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
lean_dec(x_41);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
x_48 = lean_box(0);
lean_inc(x_35);
lean_ctor_set_tag(x_25, 1);
lean_ctor_set(x_25, 1, x_48);
lean_ctor_set_tag(x_45, 1);
lean_ctor_set(x_45, 0, x_25);
x_49 = l_Lake_buildAction___redArg___lam__0(x_23, x_45, x_34);
lean_dec_ref(x_45);
lean_dec(x_23);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
lean_ctor_set(x_49, 0, x_35);
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_35);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_45);
x_54 = lean_box(0);
lean_inc(x_35);
lean_ctor_set_tag(x_25, 1);
lean_ctor_set(x_25, 1, x_54);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_25);
x_56 = l_Lake_buildAction___redArg___lam__0(x_23, x_55, x_34);
lean_dec_ref(x_55);
lean_dec(x_23);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_35);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_inc(x_39);
lean_inc_ref(x_38);
lean_inc_ref(x_36);
lean_free_object(x_25);
lean_dec(x_35);
x_60 = !lean_is_exclusive(x_34);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; 
x_61 = lean_ctor_get(x_34, 2);
lean_dec(x_61);
x_62 = lean_ctor_get(x_34, 1);
lean_dec(x_62);
x_63 = lean_ctor_get(x_34, 0);
lean_dec(x_63);
x_64 = lean_ctor_get(x_45, 0);
lean_inc(x_64);
lean_dec_ref(x_45);
x_65 = lean_io_error_to_string(x_64);
x_66 = 3;
x_67 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_66);
x_68 = lean_array_push(x_36, x_67);
lean_ctor_set(x_34, 0, x_68);
x_26 = x_41;
x_27 = x_34;
x_28 = lean_box(0);
goto block_32;
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_34);
x_69 = lean_ctor_get(x_45, 0);
lean_inc(x_69);
lean_dec_ref(x_45);
x_70 = lean_io_error_to_string(x_69);
x_71 = 3;
x_72 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set_uint8(x_72, sizeof(void*)*1, x_71);
x_73 = lean_array_push(x_36, x_72);
x_74 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_38);
lean_ctor_set(x_74, 2, x_39);
lean_ctor_set_uint8(x_74, sizeof(void*)*3, x_37);
x_26 = x_41;
x_27 = x_74;
x_28 = lean_box(0);
goto block_32;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_75 = lean_ctor_get(x_25, 1);
x_76 = lean_ctor_get(x_25, 0);
lean_inc(x_75);
lean_inc(x_76);
lean_dec(x_25);
x_77 = lean_ctor_get(x_75, 0);
x_78 = lean_ctor_get_uint8(x_75, sizeof(void*)*3);
x_79 = lean_ctor_get(x_75, 1);
x_80 = lean_ctor_get(x_75, 2);
x_81 = lean_array_get_size(x_21);
lean_dec_ref(x_21);
x_82 = lean_array_get_size(x_77);
lean_inc(x_82);
x_83 = l_Array_extract___redArg(x_77, x_81, x_82);
lean_inc(x_76);
x_84 = lean_apply_1(x_1, x_76);
x_85 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_2, x_84, x_83);
x_86 = l_Lake_BuildMetadata_writeFile(x_3, x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_82);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 x_87 = x_86;
} else {
 lean_dec_ref(x_86);
 x_87 = lean_box(0);
}
x_88 = lean_box(0);
lean_inc(x_76);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_76);
lean_ctor_set(x_89, 1, x_88);
if (lean_is_scalar(x_87)) {
 x_90 = lean_alloc_ctor(1, 1, 0);
} else {
 x_90 = x_87;
 lean_ctor_set_tag(x_90, 1);
}
lean_ctor_set(x_90, 0, x_89);
x_91 = l_Lake_buildAction___redArg___lam__0(x_23, x_90, x_75);
lean_dec_ref(x_90);
lean_dec(x_23);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_93 = x_91;
} else {
 lean_dec_ref(x_91);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_76);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_inc(x_80);
lean_inc_ref(x_79);
lean_inc_ref(x_77);
lean_dec(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 x_95 = x_75;
} else {
 lean_dec_ref(x_75);
 x_95 = lean_box(0);
}
x_96 = lean_ctor_get(x_86, 0);
lean_inc(x_96);
lean_dec_ref(x_86);
x_97 = lean_io_error_to_string(x_96);
x_98 = 3;
x_99 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set_uint8(x_99, sizeof(void*)*1, x_98);
x_100 = lean_array_push(x_77, x_99);
if (lean_is_scalar(x_95)) {
 x_101 = lean_alloc_ctor(0, 3, 1);
} else {
 x_101 = x_95;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_79);
lean_ctor_set(x_101, 2, x_80);
lean_ctor_set_uint8(x_101, sizeof(void*)*3, x_78);
x_26 = x_82;
x_27 = x_101;
x_28 = lean_box(0);
goto block_32;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec_ref(x_21);
lean_dec_ref(x_1);
x_102 = lean_ctor_get(x_25, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_25, 1);
lean_inc(x_103);
lean_dec_ref(x_25);
x_26 = x_102;
x_27 = x_103;
x_28 = lean_box(0);
goto block_32;
}
block_32:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_box(0);
x_30 = l_Lake_buildAction___redArg___lam__0(x_23, x_29, x_27);
lean_dec(x_23);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec_ref(x_30);
x_13 = x_26;
x_14 = x_31;
x_15 = lean_box(0);
goto block_17;
}
}
else
{
lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_104 = lean_ctor_get(x_11, 0);
x_105 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_106 = lean_ctor_get(x_11, 1);
x_107 = lean_ctor_get(x_11, 2);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_104);
lean_dec(x_11);
x_108 = lean_io_mono_ms_now();
x_109 = l_Lake_JobAction_merge(x_105, x_5);
lean_inc_ref(x_104);
x_110 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_110, 0, x_104);
lean_ctor_set(x_110, 1, x_106);
lean_ctor_set(x_110, 2, x_107);
lean_ctor_set_uint8(x_110, sizeof(void*)*3, x_109);
x_111 = lean_apply_7(x_4, x_6, x_7, x_8, x_9, x_10, x_110, lean_box(0));
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_119 = lean_ctor_get(x_111, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_111, 0);
lean_inc(x_120);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_121 = x_111;
} else {
 lean_dec_ref(x_111);
 x_121 = lean_box(0);
}
x_122 = lean_ctor_get(x_119, 0);
x_123 = lean_ctor_get_uint8(x_119, sizeof(void*)*3);
x_124 = lean_ctor_get(x_119, 1);
x_125 = lean_ctor_get(x_119, 2);
x_126 = lean_array_get_size(x_104);
lean_dec_ref(x_104);
x_127 = lean_array_get_size(x_122);
lean_inc(x_127);
x_128 = l_Array_extract___redArg(x_122, x_126, x_127);
lean_inc(x_120);
x_129 = lean_apply_1(x_1, x_120);
x_130 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_2, x_129, x_128);
x_131 = l_Lake_BuildMetadata_writeFile(x_3, x_130);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_127);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 x_132 = x_131;
} else {
 lean_dec_ref(x_131);
 x_132 = lean_box(0);
}
x_133 = lean_box(0);
lean_inc(x_120);
if (lean_is_scalar(x_121)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_121;
 lean_ctor_set_tag(x_134, 1);
}
lean_ctor_set(x_134, 0, x_120);
lean_ctor_set(x_134, 1, x_133);
if (lean_is_scalar(x_132)) {
 x_135 = lean_alloc_ctor(1, 1, 0);
} else {
 x_135 = x_132;
 lean_ctor_set_tag(x_135, 1);
}
lean_ctor_set(x_135, 0, x_134);
x_136 = l_Lake_buildAction___redArg___lam__0(x_108, x_135, x_119);
lean_dec_ref(x_135);
lean_dec(x_108);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_138 = x_136;
} else {
 lean_dec_ref(x_136);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_120);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_inc(x_125);
lean_inc_ref(x_124);
lean_inc_ref(x_122);
lean_dec(x_121);
lean_dec(x_120);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 lean_ctor_release(x_119, 2);
 x_140 = x_119;
} else {
 lean_dec_ref(x_119);
 x_140 = lean_box(0);
}
x_141 = lean_ctor_get(x_131, 0);
lean_inc(x_141);
lean_dec_ref(x_131);
x_142 = lean_io_error_to_string(x_141);
x_143 = 3;
x_144 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set_uint8(x_144, sizeof(void*)*1, x_143);
x_145 = lean_array_push(x_122, x_144);
if (lean_is_scalar(x_140)) {
 x_146 = lean_alloc_ctor(0, 3, 1);
} else {
 x_146 = x_140;
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_124);
lean_ctor_set(x_146, 2, x_125);
lean_ctor_set_uint8(x_146, sizeof(void*)*3, x_123);
x_112 = x_127;
x_113 = x_146;
x_114 = lean_box(0);
goto block_118;
}
}
else
{
lean_object* x_147; lean_object* x_148; 
lean_dec_ref(x_104);
lean_dec_ref(x_1);
x_147 = lean_ctor_get(x_111, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_111, 1);
lean_inc(x_148);
lean_dec_ref(x_111);
x_112 = x_147;
x_113 = x_148;
x_114 = lean_box(0);
goto block_118;
}
block_118:
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_box(0);
x_116 = l_Lake_buildAction___redArg___lam__0(x_108, x_115, x_113);
lean_dec(x_108);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec_ref(x_116);
x_13 = x_112;
x_14 = x_117;
x_15 = lean_box(0);
goto block_17;
}
}
}
else
{
uint8_t x_149; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_149 = !lean_is_exclusive(x_11);
if (x_149 == 0)
{
lean_object* x_150; uint8_t x_151; uint8_t x_152; uint8_t x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_150 = lean_ctor_get(x_11, 0);
x_151 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_152 = 3;
x_153 = l_Lake_JobAction_merge(x_151, x_152);
x_154 = l_Lake_buildAction___redArg___closed__1;
x_155 = lean_array_get_size(x_150);
x_156 = lean_array_push(x_150, x_154);
lean_ctor_set(x_11, 0, x_156);
lean_ctor_set_uint8(x_11, sizeof(void*)*3, x_153);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_11);
return x_157;
}
else
{
lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_158 = lean_ctor_get(x_11, 0);
x_159 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_160 = lean_ctor_get(x_11, 1);
x_161 = lean_ctor_get(x_11, 2);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_158);
lean_dec(x_11);
x_162 = 3;
x_163 = l_Lake_JobAction_merge(x_159, x_162);
x_164 = l_Lake_buildAction___redArg___closed__1;
x_165 = lean_array_get_size(x_158);
x_166 = lean_array_push(x_158, x_164);
x_167 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_160);
lean_ctor_set(x_167, 2, x_161);
lean_ctor_set_uint8(x_167, sizeof(void*)*3, x_163);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
block_17:
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lake_buildAction___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_buildAction___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
x_14 = l_Lake_buildAction___redArg(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_6);
x_15 = l_Lake_buildAction(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_15;
}
}
static lean_object* _init_l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instToOutputJsonPUnit___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_5);
x_18 = l_Lake_readTraceFile(x_5, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
lean_ctor_set(x_14, 0, x_20);
x_21 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_1, x_2, x_3, x_4, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = 0;
x_26 = lean_unbox(x_23);
lean_dec(x_23);
x_27 = l_Lake_instDecidableEqOutputStatus(x_26, x_25);
if (x_27 == 0)
{
uint8_t x_28; lean_object* x_29; 
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_28 = 1;
x_29 = lean_box(x_28);
lean_ctor_set(x_21, 0, x_29);
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_free_object(x_21);
x_30 = l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0;
x_31 = l_Lake_buildAction___redArg(x_30, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_24);
lean_dec_ref(x_5);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = 0;
x_35 = lean_box(x_34);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = 0;
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
return x_31;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_31, 0);
x_42 = lean_ctor_get(x_31, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_31);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; 
x_44 = lean_ctor_get(x_21, 0);
x_45 = lean_ctor_get(x_21, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_21);
x_46 = 0;
x_47 = lean_unbox(x_44);
lean_dec(x_44);
x_48 = l_Lake_instDecidableEqOutputStatus(x_47, x_46);
if (x_48 == 0)
{
uint8_t x_49; lean_object* x_50; lean_object* x_51; 
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_49 = 1;
x_50 = lean_box(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_45);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0;
x_53 = l_Lake_buildAction___redArg(x_52, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_45);
lean_dec_ref(x_5);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
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
x_56 = 0;
x_57 = lean_box(x_56);
if (lean_is_scalar(x_55)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_55;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_54);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_53, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_53, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_61 = x_53;
} else {
 lean_dec_ref(x_53);
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
}
else
{
uint8_t x_63; 
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_63 = !lean_is_exclusive(x_18);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_18, 1);
lean_ctor_set(x_14, 0, x_64);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_18, 0);
x_66 = lean_ctor_get(x_18, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_18);
lean_ctor_set(x_14, 0, x_66);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_14);
return x_67;
}
}
}
else
{
lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_14, 0);
x_69 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
x_70 = lean_ctor_get(x_14, 1);
x_71 = lean_ctor_get(x_14, 2);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_68);
lean_dec(x_14);
lean_inc_ref(x_5);
x_72 = l_Lake_readTraceFile(x_5, x_68);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec_ref(x_72);
x_75 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_70);
lean_ctor_set(x_75, 2, x_71);
lean_ctor_set_uint8(x_75, sizeof(void*)*3, x_69);
x_76 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_1, x_2, x_3, x_4, x_73, x_8, x_9, x_10, x_11, x_12, x_13, x_75);
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
x_80 = 0;
x_81 = lean_unbox(x_77);
lean_dec(x_77);
x_82 = l_Lake_instDecidableEqOutputStatus(x_81, x_80);
if (x_82 == 0)
{
uint8_t x_83; lean_object* x_84; lean_object* x_85; 
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_83 = 1;
x_84 = lean_box(x_83);
if (lean_is_scalar(x_79)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_79;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_78);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_79);
x_86 = l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0;
x_87 = l_Lake_buildAction___redArg(x_86, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_78);
lean_dec_ref(x_5);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; 
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
x_90 = 0;
x_91 = lean_box(x_90);
if (lean_is_scalar(x_89)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_89;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_88);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_87, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_87, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_95 = x_87;
} else {
 lean_dec_ref(x_87);
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
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_97 = lean_ctor_get(x_72, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_72, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_99 = x_72;
} else {
 lean_dec_ref(x_72);
 x_99 = lean_box(0);
}
x_100 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_70);
lean_ctor_set(x_100, 2, x_71);
lean_ctor_set_uint8(x_100, sizeof(void*)*3, x_69);
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_99;
}
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_6);
x_19 = l_Lake_readTraceFile(x_6, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
lean_ctor_set(x_15, 0, x_21);
x_22 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_2, x_3, x_4, x_5, x_20, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = 0;
x_27 = lean_unbox(x_24);
lean_dec(x_24);
x_28 = l_Lake_instDecidableEqOutputStatus(x_27, x_26);
if (x_28 == 0)
{
uint8_t x_29; lean_object* x_30; 
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_29 = 1;
x_30 = lean_box(x_29);
lean_ctor_set(x_22, 0, x_30);
return x_22;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_free_object(x_22);
x_31 = l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0;
x_32 = l_Lake_buildAction___redArg(x_31, x_5, x_6, x_7, x_8, x_10, x_11, x_12, x_13, x_14, x_25);
lean_dec_ref(x_6);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
x_35 = 0;
x_36 = lean_box(x_35);
lean_ctor_set(x_32, 0, x_36);
return x_32;
}
else
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = 0;
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_32);
if (x_41 == 0)
{
return x_32;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_32, 0);
x_43 = lean_ctor_get(x_32, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_32);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_22, 0);
x_46 = lean_ctor_get(x_22, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_22);
x_47 = 0;
x_48 = lean_unbox(x_45);
lean_dec(x_45);
x_49 = l_Lake_instDecidableEqOutputStatus(x_48, x_47);
if (x_49 == 0)
{
uint8_t x_50; lean_object* x_51; lean_object* x_52; 
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_50 = 1;
x_51 = lean_box(x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_46);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0;
x_54 = l_Lake_buildAction___redArg(x_53, x_5, x_6, x_7, x_8, x_10, x_11, x_12, x_13, x_14, x_46);
lean_dec_ref(x_6);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
x_57 = 0;
x_58 = lean_box(x_57);
if (lean_is_scalar(x_56)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_56;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_55);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_54, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_54, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_62 = x_54;
} else {
 lean_dec_ref(x_54);
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
}
else
{
uint8_t x_64; 
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_64 = !lean_is_exclusive(x_19);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_19, 1);
lean_ctor_set(x_15, 0, x_65);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_19, 0);
x_67 = lean_ctor_get(x_19, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_19);
lean_ctor_set(x_15, 0, x_67);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_15);
return x_68;
}
}
}
else
{
lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_15, 0);
x_70 = lean_ctor_get_uint8(x_15, sizeof(void*)*3);
x_71 = lean_ctor_get(x_15, 1);
x_72 = lean_ctor_get(x_15, 2);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_69);
lean_dec(x_15);
lean_inc_ref(x_6);
x_73 = l_Lake_readTraceFile(x_6, x_69);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec_ref(x_73);
x_76 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_71);
lean_ctor_set(x_76, 2, x_72);
lean_ctor_set_uint8(x_76, sizeof(void*)*3, x_70);
x_77 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_2, x_3, x_4, x_5, x_74, x_9, x_10, x_11, x_12, x_13, x_14, x_76);
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
x_81 = 0;
x_82 = lean_unbox(x_78);
lean_dec(x_78);
x_83 = l_Lake_instDecidableEqOutputStatus(x_82, x_81);
if (x_83 == 0)
{
uint8_t x_84; lean_object* x_85; lean_object* x_86; 
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_84 = 1;
x_85 = lean_box(x_84);
if (lean_is_scalar(x_80)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_80;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_79);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_80);
x_87 = l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0;
x_88 = l_Lake_buildAction___redArg(x_87, x_5, x_6, x_7, x_8, x_10, x_11, x_12, x_13, x_14, x_79);
lean_dec_ref(x_6);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_90 = x_88;
} else {
 lean_dec_ref(x_88);
 x_90 = lean_box(0);
}
x_91 = 0;
x_92 = lean_box(x_91);
if (lean_is_scalar(x_90)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_90;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_89);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_88, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_88, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_96 = x_88;
} else {
 lean_dec_ref(x_88);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_98 = lean_ctor_get(x_73, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_73, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_100 = x_73;
} else {
 lean_dec_ref(x_73);
 x_100 = lean_box(0);
}
x_101 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_71);
lean_ctor_set(x_101, 2, x_72);
lean_ctor_set_uint8(x_101, sizeof(void*)*3, x_70);
if (lean_is_scalar(x_100)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_100;
}
lean_ctor_set(x_102, 0, x_98);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_7);
x_17 = l_Lake_buildUnlessUpToDate_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_8);
x_18 = l_Lake_buildUnlessUpToDate_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_17, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_21; 
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_5);
x_23 = l_Lake_readTraceFile(x_5, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_35; uint8_t x_36; uint8_t x_37; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
lean_ctor_set(x_14, 0, x_25);
x_26 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_1, x_2, x_3, x_4, x_24, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
x_30 = lean_box(0);
x_35 = 0;
x_36 = lean_unbox(x_27);
lean_dec(x_27);
x_37 = l_Lake_instDecidableEqOutputStatus(x_36, x_35);
if (x_37 == 0)
{
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_31 = x_28;
x_32 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0;
x_39 = l_Lake_buildAction___redArg(x_38, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_28);
lean_dec_ref(x_5);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec_ref(x_39);
x_31 = x_40;
x_32 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_29);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec_ref(x_39);
x_16 = x_41;
x_17 = x_42;
x_18 = lean_box(0);
goto block_20;
}
}
block_34:
{
lean_object* x_33; 
if (lean_is_scalar(x_29)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_29;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_43 = lean_ctor_get(x_23, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_23, 1);
lean_inc(x_44);
lean_dec_ref(x_23);
lean_ctor_set(x_14, 0, x_44);
x_16 = x_43;
x_17 = x_14;
x_18 = lean_box(0);
goto block_20;
}
}
else
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_14, 0);
x_46 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
x_47 = lean_ctor_get(x_14, 1);
x_48 = lean_ctor_get(x_14, 2);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_45);
lean_dec(x_14);
lean_inc_ref(x_5);
x_49 = l_Lake_readTraceFile(x_5, x_45);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_62; uint8_t x_63; uint8_t x_64; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec_ref(x_49);
x_52 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_47);
lean_ctor_set(x_52, 2, x_48);
lean_ctor_set_uint8(x_52, sizeof(void*)*3, x_46);
x_53 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_1, x_2, x_3, x_4, x_50, x_8, x_9, x_10, x_11, x_12, x_13, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
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
x_57 = lean_box(0);
x_62 = 0;
x_63 = lean_unbox(x_54);
lean_dec(x_54);
x_64 = l_Lake_instDecidableEqOutputStatus(x_63, x_62);
if (x_64 == 0)
{
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_58 = x_55;
x_59 = lean_box(0);
goto block_61;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0;
x_66 = l_Lake_buildAction___redArg(x_65, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_55);
lean_dec_ref(x_5);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec_ref(x_66);
x_58 = x_67;
x_59 = lean_box(0);
goto block_61;
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_56);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec_ref(x_66);
x_16 = x_68;
x_17 = x_69;
x_18 = lean_box(0);
goto block_20;
}
}
block_61:
{
lean_object* x_60; 
if (lean_is_scalar(x_56)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_56;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_70 = lean_ctor_get(x_49, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_49, 1);
lean_inc(x_71);
lean_dec_ref(x_49);
x_72 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_47);
lean_ctor_set(x_72, 2, x_48);
lean_ctor_set_uint8(x_72, sizeof(void*)*3, x_46);
x_16 = x_70;
x_17 = x_72;
x_18 = lean_box(0);
goto block_20;
}
}
block_20:
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_6);
x_24 = l_Lake_readTraceFile(x_6, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_36; uint8_t x_37; uint8_t x_38; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
lean_ctor_set(x_15, 0, x_26);
x_27 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_2, x_3, x_4, x_5, x_25, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
x_36 = 0;
x_37 = lean_unbox(x_28);
lean_dec(x_28);
x_38 = l_Lake_instDecidableEqOutputStatus(x_37, x_36);
if (x_38 == 0)
{
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_32 = x_29;
x_33 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0;
x_40 = l_Lake_buildAction___redArg(x_39, x_5, x_6, x_7, x_8, x_10, x_11, x_12, x_13, x_14, x_29);
lean_dec_ref(x_6);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec_ref(x_40);
x_32 = x_41;
x_33 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_30);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec_ref(x_40);
x_17 = x_42;
x_18 = x_43;
x_19 = lean_box(0);
goto block_21;
}
}
block_35:
{
lean_object* x_34; 
if (lean_is_scalar(x_30)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_30;
}
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_44 = lean_ctor_get(x_24, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_24, 1);
lean_inc(x_45);
lean_dec_ref(x_24);
lean_ctor_set(x_15, 0, x_45);
x_17 = x_44;
x_18 = x_15;
x_19 = lean_box(0);
goto block_21;
}
}
else
{
lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_15, 0);
x_47 = lean_ctor_get_uint8(x_15, sizeof(void*)*3);
x_48 = lean_ctor_get(x_15, 1);
x_49 = lean_ctor_get(x_15, 2);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_46);
lean_dec(x_15);
lean_inc_ref(x_6);
x_50 = l_Lake_readTraceFile(x_6, x_46);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_63; uint8_t x_64; uint8_t x_65; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec_ref(x_50);
x_53 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_48);
lean_ctor_set(x_53, 2, x_49);
lean_ctor_set_uint8(x_53, sizeof(void*)*3, x_47);
x_54 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_2, x_3, x_4, x_5, x_51, x_9, x_10, x_11, x_12, x_13, x_14, x_53);
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
x_58 = lean_box(0);
x_63 = 0;
x_64 = lean_unbox(x_55);
lean_dec(x_55);
x_65 = l_Lake_instDecidableEqOutputStatus(x_64, x_63);
if (x_65 == 0)
{
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_59 = x_56;
x_60 = lean_box(0);
goto block_62;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0;
x_67 = l_Lake_buildAction___redArg(x_66, x_5, x_6, x_7, x_8, x_10, x_11, x_12, x_13, x_14, x_56);
lean_dec_ref(x_6);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec_ref(x_67);
x_59 = x_68;
x_60 = lean_box(0);
goto block_62;
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_57);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec_ref(x_67);
x_17 = x_69;
x_18 = x_70;
x_19 = lean_box(0);
goto block_21;
}
}
block_62:
{
lean_object* x_61; 
if (lean_is_scalar(x_57)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_57;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_71 = lean_ctor_get(x_50, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_50, 1);
lean_inc(x_72);
lean_dec_ref(x_50);
x_73 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_48);
lean_ctor_set(x_73, 2, x_49);
lean_ctor_set_uint8(x_73, sizeof(void*)*3, x_47);
x_17 = x_71;
x_18 = x_73;
x_19 = lean_box(0);
goto block_21;
}
}
block_21:
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_7);
x_17 = l_Lake_buildUnlessUpToDate___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_8);
x_18 = l_Lake_buildUnlessUpToDate(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_17, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
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
LEAN_EXPORT lean_object* l_Lake_writeFileHash(lean_object* x_1, uint64_t x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lake_writeFileHash___closed__0;
x_5 = lean_string_append(x_1, x_4);
x_6 = l_Lake_createParentDirs(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_6);
x_7 = l_Lake_Hash_hex(x_2);
x_8 = l_IO_FS_writeFile(x_5, x_7);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
return x_8;
}
else
{
lean_dec_ref(x_5);
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
x_5 = l_Lake_writeFileHash(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheFileHash(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_4; 
if (x_2 == 0)
{
lean_object* x_12; 
x_12 = l_Lake_computeBinFileHash(x_1);
x_4 = x_12;
goto block_11;
}
else
{
lean_object* x_13; 
x_13 = l_Lake_computeTextFileHash(x_1);
x_4 = x_13;
goto block_11;
}
block_11:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; uint64_t x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_unbox_uint64(x_5);
lean_dec(x_5);
x_7 = l_Lake_writeFileHash(x_1, x_6);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec_ref(x_1);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
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
x_5 = l_Lake_cacheFileHash(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_clearFileHash(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lake_writeFileHash___closed__0;
x_4 = lean_string_append(x_1, x_3);
x_5 = l_Lake_removeFileIfExists(x_4);
lean_dec_ref(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_clearFileHash___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_clearFileHash(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_47; lean_object* x_48; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 1);
x_8 = l_Lake_writeFileHash___closed__0;
lean_inc_ref(x_1);
x_9 = lean_string_append(x_1, x_8);
if (x_7 == 0)
{
x_47 = x_4;
x_48 = lean_box(0);
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = l_Lake_Hash_load_x3f(x_9);
if (lean_obj_tag(x_60) == 0)
{
x_47 = x_4;
x_48 = lean_box(0);
goto block_59;
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec_ref(x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_4);
return x_62;
}
}
block_46:
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lake_createParentDirs(x_9);
if (lean_obj_tag(x_16) == 0)
{
uint64_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_16);
x_17 = lean_unbox_uint64(x_15);
x_18 = l_Lake_Hash_hex(x_17);
x_19 = l_IO_FS_writeFile(x_9, x_18);
lean_dec_ref(x_18);
lean_dec_ref(x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_19);
x_20 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_10);
lean_ctor_set(x_20, 2, x_12);
lean_ctor_set_uint8(x_20, sizeof(void*)*3, x_13);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_15);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec_ref(x_19);
x_23 = lean_io_error_to_string(x_22);
x_24 = 3;
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
x_26 = lean_array_get_size(x_11);
x_27 = lean_array_push(x_11, x_25);
x_28 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_10);
lean_ctor_set(x_28, 2, x_12);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_13);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_15);
lean_dec_ref(x_9);
x_30 = lean_ctor_get(x_16, 0);
lean_inc(x_30);
lean_dec_ref(x_16);
x_31 = lean_io_error_to_string(x_30);
x_32 = 3;
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
x_34 = lean_array_get_size(x_11);
x_35 = lean_array_push(x_11, x_33);
x_36 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_10);
lean_ctor_set(x_36, 2, x_12);
lean_ctor_set_uint8(x_36, sizeof(void*)*3, x_13);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_9);
x_38 = lean_ctor_get(x_14, 0);
lean_inc(x_38);
lean_dec_ref(x_14);
x_39 = lean_io_error_to_string(x_38);
x_40 = 3;
x_41 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_40);
x_42 = lean_array_get_size(x_11);
x_43 = lean_array_push(x_11, x_41);
x_44 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_10);
lean_ctor_set(x_44, 2, x_12);
lean_ctor_set_uint8(x_44, sizeof(void*)*3, x_13);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
block_59:
{
if (x_2 == 0)
{
lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_47, 0);
lean_inc_ref(x_49);
x_50 = lean_ctor_get_uint8(x_47, sizeof(void*)*3);
x_51 = lean_ctor_get(x_47, 1);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_47, 2);
lean_inc(x_52);
lean_dec_ref(x_47);
x_53 = l_Lake_computeBinFileHash(x_1);
lean_dec_ref(x_1);
x_10 = x_51;
x_11 = x_49;
x_12 = x_52;
x_13 = x_50;
x_14 = x_53;
goto block_46;
}
else
{
lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_47, 0);
lean_inc_ref(x_54);
x_55 = lean_ctor_get_uint8(x_47, sizeof(void*)*3);
x_56 = lean_ctor_get(x_47, 1);
lean_inc_ref(x_56);
x_57 = lean_ctor_get(x_47, 2);
lean_inc(x_57);
lean_dec_ref(x_47);
x_58 = l_Lake_computeTextFileHash(x_1);
lean_dec_ref(x_1);
x_10 = x_56;
x_11 = x_54;
x_12 = x_57;
x_13 = x_55;
x_14 = x_58;
goto block_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_fetchFileHash___redArg(x_1, x_2, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lake_fetchFileHash___redArg(x_1, x_6, x_3, x_4);
lean_dec_ref(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_Lake_fetchFileHash(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
lean_inc_ref(x_1);
x_6 = l_Lake_fetchFileHash___redArg(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_12 = lean_ctor_get(x_8, 1);
x_13 = lean_ctor_get(x_8, 2);
x_14 = lean_io_metadata(x_1);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_16);
lean_dec(x_15);
x_17 = l_Lake_platformTrace___closed__4;
x_18 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_16);
x_19 = lean_unbox_uint64(x_9);
lean_dec(x_9);
lean_ctor_set_uint64(x_18, sizeof(void*)*3, x_19);
lean_ctor_set(x_6, 0, x_18);
return x_6;
}
else
{
uint8_t x_20; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_1);
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_8, 2);
lean_dec(x_21);
x_22 = lean_ctor_get(x_8, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_8, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
lean_dec_ref(x_14);
x_25 = lean_io_error_to_string(x_24);
x_26 = 3;
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
x_28 = lean_array_get_size(x_10);
x_29 = lean_array_push(x_10, x_27);
lean_ctor_set(x_8, 0, x_29);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_28);
return x_6;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_8);
x_30 = lean_ctor_get(x_14, 0);
lean_inc(x_30);
lean_dec_ref(x_14);
x_31 = lean_io_error_to_string(x_30);
x_32 = 3;
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
x_34 = lean_array_get_size(x_10);
x_35 = lean_array_push(x_10, x_33);
x_36 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_12);
lean_ctor_set(x_36, 2, x_13);
lean_ctor_set_uint8(x_36, sizeof(void*)*3, x_11);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 1, x_36);
lean_ctor_set(x_6, 0, x_34);
return x_6;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_6, 1);
x_38 = lean_ctor_get(x_6, 0);
lean_inc(x_37);
lean_inc(x_38);
lean_dec(x_6);
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get_uint8(x_37, sizeof(void*)*3);
x_41 = lean_ctor_get(x_37, 1);
x_42 = lean_ctor_get(x_37, 2);
x_43 = lean_io_metadata(x_1);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint64_t x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = lean_ctor_get(x_44, 1);
lean_inc_ref(x_45);
lean_dec(x_44);
x_46 = l_Lake_platformTrace___closed__4;
x_47 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_47, 2, x_45);
x_48 = lean_unbox_uint64(x_38);
lean_dec(x_38);
lean_ctor_set_uint64(x_47, sizeof(void*)*3, x_48);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_37);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_inc(x_42);
lean_inc_ref(x_41);
lean_inc_ref(x_39);
lean_dec(x_38);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 x_50 = x_37;
} else {
 lean_dec_ref(x_37);
 x_50 = lean_box(0);
}
x_51 = lean_ctor_get(x_43, 0);
lean_inc(x_51);
lean_dec_ref(x_43);
x_52 = lean_io_error_to_string(x_51);
x_53 = 3;
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_53);
x_55 = lean_array_get_size(x_39);
x_56 = lean_array_push(x_39, x_54);
if (lean_is_scalar(x_50)) {
 x_57 = lean_alloc_ctor(0, 3, 1);
} else {
 x_57 = x_50;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_41);
lean_ctor_set(x_57, 2, x_42);
lean_ctor_set_uint8(x_57, sizeof(void*)*3, x_40);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec_ref(x_1);
x_59 = !lean_is_exclusive(x_6);
if (x_59 == 0)
{
return x_6;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_6, 0);
x_61 = lean_ctor_get(x_6, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_6);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_fetchFileTrace___redArg(x_1, x_2, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lake_fetchFileTrace___redArg(x_1, x_6, x_3, x_4);
lean_dec_ref(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_Lake_fetchFileTrace(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at_____private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___at_____private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_metadata(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = l_IO_FS_instOrdSystemTime_ord(x_2, x_6);
lean_dec_ref(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
else
{
uint8_t x_10; 
lean_dec_ref(x_4);
x_10 = 0;
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint64_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
x_9 = lean_box_uint64(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Option_instBEq_beq___at_____private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__0(x_10, x_3);
lean_dec_ref(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get_uint8(x_12, sizeof(void*)*2);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = l_Lake_MTime_checkUpToDate___at_____private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__1(x_1, x_4);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
else
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_21 = 1;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
}
}
else
{
uint8_t x_24; 
x_24 = l_System_FilePath_pathExists(x_1);
if (x_24 == 0)
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_25 = 0;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_6);
return x_27;
}
else
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_28 = 2;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_6);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_4) == 2)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; uint64_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_25; uint8_t x_26; uint8_t x_27; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get_uint64(x_13, sizeof(void*)*3);
x_15 = lean_ctor_get(x_13, 2);
lean_inc_ref(x_15);
lean_dec_ref(x_13);
x_16 = lean_box_uint64(x_14);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_16);
x_17 = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_9, x_10);
lean_dec_ref(x_4);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_20 = x_17;
} else {
 lean_dec_ref(x_17);
 x_20 = lean_box(0);
}
x_25 = 0;
x_26 = lean_unbox(x_18);
x_27 = l_Lake_instDecidableEqOutputStatus(x_26, x_25);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
uint8_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get_uint8(x_19, sizeof(void*)*3);
x_30 = 1;
x_31 = l_Lake_JobAction_merge(x_29, x_30);
lean_ctor_set_uint8(x_19, sizeof(void*)*3, x_31);
x_32 = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(x_15, x_1, x_6, x_7, x_8, x_9, x_19);
lean_dec_ref(x_15);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec_ref(x_32);
x_21 = x_33;
x_22 = lean_box(0);
goto block_24;
}
else
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get_uint8(x_19, sizeof(void*)*3);
x_36 = lean_ctor_get(x_19, 1);
x_37 = lean_ctor_get(x_19, 2);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_34);
lean_dec(x_19);
x_38 = 1;
x_39 = l_Lake_JobAction_merge(x_35, x_38);
x_40 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_36);
lean_ctor_set(x_40, 2, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*3, x_39);
x_41 = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(x_15, x_1, x_6, x_7, x_8, x_9, x_40);
lean_dec_ref(x_15);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec_ref(x_41);
x_21 = x_42;
x_22 = lean_box(0);
goto block_24;
}
}
else
{
lean_dec_ref(x_15);
x_21 = x_19;
x_22 = lean_box(0);
goto block_24;
}
block_24:
{
lean_object* x_23; 
if (lean_is_scalar(x_20)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_20;
}
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_43; uint64_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_56; uint8_t x_57; uint8_t x_58; 
x_43 = lean_ctor_get(x_4, 0);
lean_inc(x_43);
lean_dec(x_4);
x_44 = lean_ctor_get_uint64(x_43, sizeof(void*)*3);
x_45 = lean_ctor_get(x_43, 2);
lean_inc_ref(x_45);
lean_dec_ref(x_43);
x_46 = lean_box_uint64(x_44);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(x_2, x_3, x_47, x_5, x_9, x_10);
lean_dec_ref(x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
x_56 = 0;
x_57 = lean_unbox(x_49);
x_58 = l_Lake_instDecidableEqOutputStatus(x_57, x_56);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_59 = lean_ctor_get(x_50, 0);
lean_inc_ref(x_59);
x_60 = lean_ctor_get_uint8(x_50, sizeof(void*)*3);
x_61 = lean_ctor_get(x_50, 1);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_50, 2);
lean_inc(x_62);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 lean_ctor_release(x_50, 2);
 x_63 = x_50;
} else {
 lean_dec_ref(x_50);
 x_63 = lean_box(0);
}
x_64 = 1;
x_65 = l_Lake_JobAction_merge(x_60, x_64);
if (lean_is_scalar(x_63)) {
 x_66 = lean_alloc_ctor(0, 3, 1);
} else {
 x_66 = x_63;
}
lean_ctor_set(x_66, 0, x_59);
lean_ctor_set(x_66, 1, x_61);
lean_ctor_set(x_66, 2, x_62);
lean_ctor_set_uint8(x_66, sizeof(void*)*3, x_65);
x_67 = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(x_45, x_1, x_6, x_7, x_8, x_9, x_66);
lean_dec_ref(x_45);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec_ref(x_67);
x_52 = x_68;
x_53 = lean_box(0);
goto block_55;
}
else
{
lean_dec_ref(x_45);
x_52 = x_50;
x_53 = lean_box(0);
goto block_55;
}
block_55:
{
lean_object* x_54; 
if (lean_is_scalar(x_51)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_51;
}
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
else
{
lean_object* x_69; uint8_t x_70; 
lean_dec(x_4);
x_69 = lean_ctor_get(x_9, 0);
x_70 = lean_ctor_get_uint8(x_69, sizeof(void*)*2);
if (x_70 == 0)
{
uint8_t x_71; lean_object* x_72; lean_object* x_73; 
x_71 = 0;
x_72 = lean_box(x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_10);
return x_73;
}
else
{
uint8_t x_74; 
x_74 = l_Lake_MTime_checkUpToDate___at_____private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__1(x_2, x_5);
if (x_74 == 0)
{
uint8_t x_75; lean_object* x_76; lean_object* x_77; 
x_75 = 0;
x_76 = lean_box(x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_10);
return x_77;
}
else
{
uint8_t x_78; lean_object* x_79; lean_object* x_80; 
x_78 = 1;
x_79 = lean_box(x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_10);
return x_80;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__4___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_io_mono_ms_now();
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_nat_sub(x_5, x_1);
lean_dec(x_5);
x_9 = lean_box(0);
x_10 = lean_nat_add(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
lean_ctor_set(x_3, 2, x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_12);
lean_dec(x_3);
x_16 = lean_nat_sub(x_5, x_1);
lean_dec(x_5);
x_17 = lean_box(0);
x_18 = lean_nat_add(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*3, x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get_uint8(x_18, sizeof(void*)*2 + 2);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_23 = lean_io_mono_ms_now();
x_24 = l_Lake_JobAction_merge(x_22, x_6);
lean_inc_ref(x_21);
lean_ctor_set_uint8(x_11, sizeof(void*)*3, x_24);
x_25 = lean_apply_7(x_1, x_3, x_7, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_25);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_25, 1);
x_35 = lean_ctor_get(x_25, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get_uint8(x_34, sizeof(void*)*3);
x_38 = lean_ctor_get(x_34, 1);
x_39 = lean_ctor_get(x_34, 2);
x_40 = l_Lake_clearFileHash(x_2);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = lean_array_get_size(x_21);
lean_dec_ref(x_21);
x_43 = lean_array_get_size(x_36);
lean_inc(x_43);
x_44 = l_Array_extract___redArg(x_36, x_42, x_43);
x_45 = lean_box(0);
x_46 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_4, x_45, x_44);
x_47 = l_Lake_BuildMetadata_writeFile(x_5, x_46);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
lean_dec(x_43);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
x_50 = lean_box(0);
lean_inc(x_41);
lean_ctor_set_tag(x_25, 1);
lean_ctor_set(x_25, 1, x_50);
lean_ctor_set(x_25, 0, x_41);
lean_ctor_set_tag(x_47, 1);
lean_ctor_set(x_47, 0, x_25);
x_51 = l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__4___lam__0(x_23, x_47, x_34);
lean_dec_ref(x_47);
lean_dec(x_23);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
lean_ctor_set(x_51, 0, x_41);
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_41);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_47);
x_56 = lean_box(0);
lean_inc(x_41);
lean_ctor_set_tag(x_25, 1);
lean_ctor_set(x_25, 1, x_56);
lean_ctor_set(x_25, 0, x_41);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_25);
x_58 = l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__4___lam__0(x_23, x_57, x_34);
lean_dec_ref(x_57);
lean_dec(x_23);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_41);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec(x_41);
lean_inc(x_39);
lean_inc_ref(x_38);
lean_inc_ref(x_36);
lean_free_object(x_25);
x_62 = !lean_is_exclusive(x_34);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; 
x_63 = lean_ctor_get(x_34, 2);
lean_dec(x_63);
x_64 = lean_ctor_get(x_34, 1);
lean_dec(x_64);
x_65 = lean_ctor_get(x_34, 0);
lean_dec(x_65);
x_66 = lean_ctor_get(x_47, 0);
lean_inc(x_66);
lean_dec_ref(x_47);
x_67 = lean_io_error_to_string(x_66);
x_68 = 3;
x_69 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set_uint8(x_69, sizeof(void*)*1, x_68);
x_70 = lean_array_push(x_36, x_69);
lean_ctor_set(x_34, 0, x_70);
x_26 = x_43;
x_27 = x_34;
x_28 = lean_box(0);
goto block_32;
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_34);
x_71 = lean_ctor_get(x_47, 0);
lean_inc(x_71);
lean_dec_ref(x_47);
x_72 = lean_io_error_to_string(x_71);
x_73 = 3;
x_74 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set_uint8(x_74, sizeof(void*)*1, x_73);
x_75 = lean_array_push(x_36, x_74);
x_76 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_38);
lean_ctor_set(x_76, 2, x_39);
lean_ctor_set_uint8(x_76, sizeof(void*)*3, x_37);
x_26 = x_43;
x_27 = x_76;
x_28 = lean_box(0);
goto block_32;
}
}
}
else
{
uint8_t x_77; 
lean_inc(x_39);
lean_inc_ref(x_38);
lean_inc_ref(x_36);
lean_free_object(x_25);
lean_dec_ref(x_21);
x_77 = !lean_is_exclusive(x_34);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_78 = lean_ctor_get(x_34, 2);
lean_dec(x_78);
x_79 = lean_ctor_get(x_34, 1);
lean_dec(x_79);
x_80 = lean_ctor_get(x_34, 0);
lean_dec(x_80);
x_81 = lean_ctor_get(x_40, 0);
lean_inc(x_81);
lean_dec_ref(x_40);
x_82 = lean_io_error_to_string(x_81);
x_83 = 3;
x_84 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set_uint8(x_84, sizeof(void*)*1, x_83);
x_85 = lean_array_get_size(x_36);
x_86 = lean_array_push(x_36, x_84);
lean_ctor_set(x_34, 0, x_86);
x_26 = x_85;
x_27 = x_34;
x_28 = lean_box(0);
goto block_32;
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_34);
x_87 = lean_ctor_get(x_40, 0);
lean_inc(x_87);
lean_dec_ref(x_40);
x_88 = lean_io_error_to_string(x_87);
x_89 = 3;
x_90 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set_uint8(x_90, sizeof(void*)*1, x_89);
x_91 = lean_array_get_size(x_36);
x_92 = lean_array_push(x_36, x_90);
x_93 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_38);
lean_ctor_set(x_93, 2, x_39);
lean_ctor_set_uint8(x_93, sizeof(void*)*3, x_37);
x_26 = x_91;
x_27 = x_93;
x_28 = lean_box(0);
goto block_32;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_25, 1);
lean_inc(x_94);
lean_dec(x_25);
x_95 = lean_ctor_get(x_94, 0);
x_96 = lean_ctor_get_uint8(x_94, sizeof(void*)*3);
x_97 = lean_ctor_get(x_94, 1);
x_98 = lean_ctor_get(x_94, 2);
x_99 = l_Lake_clearFileHash(x_2);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec_ref(x_99);
x_101 = lean_array_get_size(x_21);
lean_dec_ref(x_21);
x_102 = lean_array_get_size(x_95);
lean_inc(x_102);
x_103 = l_Array_extract___redArg(x_95, x_101, x_102);
x_104 = lean_box(0);
x_105 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_4, x_104, x_103);
x_106 = l_Lake_BuildMetadata_writeFile(x_5, x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_102);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 x_107 = x_106;
} else {
 lean_dec_ref(x_106);
 x_107 = lean_box(0);
}
x_108 = lean_box(0);
lean_inc(x_100);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_100);
lean_ctor_set(x_109, 1, x_108);
if (lean_is_scalar(x_107)) {
 x_110 = lean_alloc_ctor(1, 1, 0);
} else {
 x_110 = x_107;
 lean_ctor_set_tag(x_110, 1);
}
lean_ctor_set(x_110, 0, x_109);
x_111 = l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__4___lam__0(x_23, x_110, x_94);
lean_dec_ref(x_110);
lean_dec(x_23);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_113 = x_111;
} else {
 lean_dec_ref(x_111);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_100);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_100);
lean_inc(x_98);
lean_inc_ref(x_97);
lean_inc_ref(x_95);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 lean_ctor_release(x_94, 2);
 x_115 = x_94;
} else {
 lean_dec_ref(x_94);
 x_115 = lean_box(0);
}
x_116 = lean_ctor_get(x_106, 0);
lean_inc(x_116);
lean_dec_ref(x_106);
x_117 = lean_io_error_to_string(x_116);
x_118 = 3;
x_119 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set_uint8(x_119, sizeof(void*)*1, x_118);
x_120 = lean_array_push(x_95, x_119);
if (lean_is_scalar(x_115)) {
 x_121 = lean_alloc_ctor(0, 3, 1);
} else {
 x_121 = x_115;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_97);
lean_ctor_set(x_121, 2, x_98);
lean_ctor_set_uint8(x_121, sizeof(void*)*3, x_96);
x_26 = x_102;
x_27 = x_121;
x_28 = lean_box(0);
goto block_32;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_inc(x_98);
lean_inc_ref(x_97);
lean_inc_ref(x_95);
lean_dec_ref(x_21);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 lean_ctor_release(x_94, 2);
 x_122 = x_94;
} else {
 lean_dec_ref(x_94);
 x_122 = lean_box(0);
}
x_123 = lean_ctor_get(x_99, 0);
lean_inc(x_123);
lean_dec_ref(x_99);
x_124 = lean_io_error_to_string(x_123);
x_125 = 3;
x_126 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set_uint8(x_126, sizeof(void*)*1, x_125);
x_127 = lean_array_get_size(x_95);
x_128 = lean_array_push(x_95, x_126);
if (lean_is_scalar(x_122)) {
 x_129 = lean_alloc_ctor(0, 3, 1);
} else {
 x_129 = x_122;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_97);
lean_ctor_set(x_129, 2, x_98);
lean_ctor_set_uint8(x_129, sizeof(void*)*3, x_96);
x_26 = x_127;
x_27 = x_129;
x_28 = lean_box(0);
goto block_32;
}
}
}
else
{
lean_object* x_130; lean_object* x_131; 
lean_dec_ref(x_21);
lean_dec_ref(x_2);
x_130 = lean_ctor_get(x_25, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_25, 1);
lean_inc(x_131);
lean_dec_ref(x_25);
x_26 = x_130;
x_27 = x_131;
x_28 = lean_box(0);
goto block_32;
}
block_32:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_box(0);
x_30 = l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__4___lam__0(x_23, x_29, x_27);
lean_dec(x_23);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec_ref(x_30);
x_13 = x_26;
x_14 = x_31;
x_15 = lean_box(0);
goto block_17;
}
}
else
{
lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_132 = lean_ctor_get(x_11, 0);
x_133 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_134 = lean_ctor_get(x_11, 1);
x_135 = lean_ctor_get(x_11, 2);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_132);
lean_dec(x_11);
x_136 = lean_io_mono_ms_now();
x_137 = l_Lake_JobAction_merge(x_133, x_6);
lean_inc_ref(x_132);
x_138 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_138, 0, x_132);
lean_ctor_set(x_138, 1, x_134);
lean_ctor_set(x_138, 2, x_135);
lean_ctor_set_uint8(x_138, sizeof(void*)*3, x_137);
x_139 = lean_apply_7(x_1, x_3, x_7, x_8, x_9, x_10, x_138, lean_box(0));
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_147 = lean_ctor_get(x_139, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_148 = x_139;
} else {
 lean_dec_ref(x_139);
 x_148 = lean_box(0);
}
x_149 = lean_ctor_get(x_147, 0);
x_150 = lean_ctor_get_uint8(x_147, sizeof(void*)*3);
x_151 = lean_ctor_get(x_147, 1);
x_152 = lean_ctor_get(x_147, 2);
x_153 = l_Lake_clearFileHash(x_2);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
lean_dec_ref(x_153);
x_155 = lean_array_get_size(x_132);
lean_dec_ref(x_132);
x_156 = lean_array_get_size(x_149);
lean_inc(x_156);
x_157 = l_Array_extract___redArg(x_149, x_155, x_156);
x_158 = lean_box(0);
x_159 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_4, x_158, x_157);
x_160 = l_Lake_BuildMetadata_writeFile(x_5, x_159);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_156);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 x_161 = x_160;
} else {
 lean_dec_ref(x_160);
 x_161 = lean_box(0);
}
x_162 = lean_box(0);
lean_inc(x_154);
if (lean_is_scalar(x_148)) {
 x_163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_163 = x_148;
 lean_ctor_set_tag(x_163, 1);
}
lean_ctor_set(x_163, 0, x_154);
lean_ctor_set(x_163, 1, x_162);
if (lean_is_scalar(x_161)) {
 x_164 = lean_alloc_ctor(1, 1, 0);
} else {
 x_164 = x_161;
 lean_ctor_set_tag(x_164, 1);
}
lean_ctor_set(x_164, 0, x_163);
x_165 = l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__4___lam__0(x_136, x_164, x_147);
lean_dec_ref(x_164);
lean_dec(x_136);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_167 = x_165;
} else {
 lean_dec_ref(x_165);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_154);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_154);
lean_inc(x_152);
lean_inc_ref(x_151);
lean_inc_ref(x_149);
lean_dec(x_148);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 lean_ctor_release(x_147, 2);
 x_169 = x_147;
} else {
 lean_dec_ref(x_147);
 x_169 = lean_box(0);
}
x_170 = lean_ctor_get(x_160, 0);
lean_inc(x_170);
lean_dec_ref(x_160);
x_171 = lean_io_error_to_string(x_170);
x_172 = 3;
x_173 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set_uint8(x_173, sizeof(void*)*1, x_172);
x_174 = lean_array_push(x_149, x_173);
if (lean_is_scalar(x_169)) {
 x_175 = lean_alloc_ctor(0, 3, 1);
} else {
 x_175 = x_169;
}
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_151);
lean_ctor_set(x_175, 2, x_152);
lean_ctor_set_uint8(x_175, sizeof(void*)*3, x_150);
x_140 = x_156;
x_141 = x_175;
x_142 = lean_box(0);
goto block_146;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_inc(x_152);
lean_inc_ref(x_151);
lean_inc_ref(x_149);
lean_dec(x_148);
lean_dec_ref(x_132);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 lean_ctor_release(x_147, 2);
 x_176 = x_147;
} else {
 lean_dec_ref(x_147);
 x_176 = lean_box(0);
}
x_177 = lean_ctor_get(x_153, 0);
lean_inc(x_177);
lean_dec_ref(x_153);
x_178 = lean_io_error_to_string(x_177);
x_179 = 3;
x_180 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set_uint8(x_180, sizeof(void*)*1, x_179);
x_181 = lean_array_get_size(x_149);
x_182 = lean_array_push(x_149, x_180);
if (lean_is_scalar(x_176)) {
 x_183 = lean_alloc_ctor(0, 3, 1);
} else {
 x_183 = x_176;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_151);
lean_ctor_set(x_183, 2, x_152);
lean_ctor_set_uint8(x_183, sizeof(void*)*3, x_150);
x_140 = x_181;
x_141 = x_183;
x_142 = lean_box(0);
goto block_146;
}
}
else
{
lean_object* x_184; lean_object* x_185; 
lean_dec_ref(x_132);
lean_dec_ref(x_2);
x_184 = lean_ctor_get(x_139, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_139, 1);
lean_inc(x_185);
lean_dec_ref(x_139);
x_140 = x_184;
x_141 = x_185;
x_142 = lean_box(0);
goto block_146;
}
block_146:
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_box(0);
x_144 = l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__4___lam__0(x_136, x_143, x_141);
lean_dec(x_136);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec_ref(x_144);
x_13 = x_140;
x_14 = x_145;
x_15 = lean_box(0);
goto block_17;
}
}
}
else
{
uint8_t x_186; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_186 = !lean_is_exclusive(x_11);
if (x_186 == 0)
{
lean_object* x_187; uint8_t x_188; uint8_t x_189; uint8_t x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_187 = lean_ctor_get(x_11, 0);
x_188 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_189 = 3;
x_190 = l_Lake_JobAction_merge(x_188, x_189);
x_191 = l_Lake_buildAction___redArg___closed__1;
x_192 = lean_array_get_size(x_187);
x_193 = lean_array_push(x_187, x_191);
lean_ctor_set(x_11, 0, x_193);
lean_ctor_set_uint8(x_11, sizeof(void*)*3, x_190);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_11);
return x_194;
}
else
{
lean_object* x_195; uint8_t x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; uint8_t x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_195 = lean_ctor_get(x_11, 0);
x_196 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_197 = lean_ctor_get(x_11, 1);
x_198 = lean_ctor_get(x_11, 2);
lean_inc(x_198);
lean_inc(x_197);
lean_inc(x_195);
lean_dec(x_11);
x_199 = 3;
x_200 = l_Lake_JobAction_merge(x_196, x_199);
x_201 = l_Lake_buildAction___redArg___closed__1;
x_202 = lean_array_get_size(x_195);
x_203 = lean_array_push(x_195, x_201);
x_204 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_197);
lean_ctor_set(x_204, 2, x_198);
lean_ctor_set_uint8(x_204, sizeof(void*)*3, x_200);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_202);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
}
block_17:
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
return x_16;
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
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_16; lean_object* x_17; uint8_t x_45; 
x_45 = !lean_is_exclusive(x_9);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_9, 0);
x_47 = lean_ctor_get(x_9, 1);
x_48 = l_Lake_buildFileUnlessUpToDate_x27___closed__0;
lean_inc_ref(x_1);
x_49 = lean_string_append(x_1, x_48);
lean_inc_ref(x_49);
x_50 = l_Lake_readTraceFile(x_49, x_46);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec_ref(x_50);
x_53 = lean_ctor_get(x_47, 2);
lean_inc_ref(x_47);
lean_ctor_set(x_9, 0, x_52);
x_54 = l_Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0(x_4, x_1, x_47, x_51, x_53, x_5, x_6, x_7, x_8, x_9);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec_ref(x_54);
x_57 = 0;
x_58 = lean_unbox(x_55);
lean_dec(x_55);
x_59 = l_Lake_instDecidableEqOutputStatus(x_58, x_57);
if (x_59 == 0)
{
lean_dec_ref(x_49);
lean_dec_ref(x_47);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_16 = x_56;
x_17 = lean_box(0);
goto block_44;
}
else
{
uint8_t x_60; lean_object* x_61; 
x_60 = 3;
lean_inc_ref(x_8);
lean_inc_ref(x_1);
x_61 = l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__4(x_2, x_1, x_4, x_47, x_49, x_60, x_5, x_6, x_7, x_8, x_56);
lean_dec_ref(x_49);
lean_dec_ref(x_47);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec_ref(x_61);
x_16 = x_62;
x_17 = lean_box(0);
goto block_44;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec_ref(x_61);
x_11 = x_63;
x_12 = x_64;
x_13 = lean_box(0);
goto block_15;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec_ref(x_49);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_65 = lean_ctor_get(x_50, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_50, 1);
lean_inc(x_66);
lean_dec_ref(x_50);
lean_ctor_set(x_9, 0, x_66);
x_11 = x_65;
x_12 = x_9;
x_13 = lean_box(0);
goto block_15;
}
}
else
{
lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_67 = lean_ctor_get(x_9, 0);
x_68 = lean_ctor_get_uint8(x_9, sizeof(void*)*3);
x_69 = lean_ctor_get(x_9, 1);
x_70 = lean_ctor_get(x_9, 2);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_67);
lean_dec(x_9);
x_71 = l_Lake_buildFileUnlessUpToDate_x27___closed__0;
lean_inc_ref(x_1);
x_72 = lean_string_append(x_1, x_71);
lean_inc_ref(x_72);
x_73 = l_Lake_readTraceFile(x_72, x_67);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec_ref(x_73);
x_76 = lean_ctor_get(x_69, 2);
lean_inc_ref(x_69);
x_77 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_69);
lean_ctor_set(x_77, 2, x_70);
lean_ctor_set_uint8(x_77, sizeof(void*)*3, x_68);
x_78 = l_Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0(x_4, x_1, x_69, x_74, x_76, x_5, x_6, x_7, x_8, x_77);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec_ref(x_78);
x_81 = 0;
x_82 = lean_unbox(x_79);
lean_dec(x_79);
x_83 = l_Lake_instDecidableEqOutputStatus(x_82, x_81);
if (x_83 == 0)
{
lean_dec_ref(x_72);
lean_dec_ref(x_69);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_16 = x_80;
x_17 = lean_box(0);
goto block_44;
}
else
{
uint8_t x_84; lean_object* x_85; 
x_84 = 3;
lean_inc_ref(x_8);
lean_inc_ref(x_1);
x_85 = l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__4(x_2, x_1, x_4, x_69, x_72, x_84, x_5, x_6, x_7, x_8, x_80);
lean_dec_ref(x_72);
lean_dec_ref(x_69);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec_ref(x_85);
x_16 = x_86;
x_17 = lean_box(0);
goto block_44;
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_dec_ref(x_85);
x_11 = x_87;
x_12 = x_88;
x_13 = lean_box(0);
goto block_15;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec_ref(x_72);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_89 = lean_ctor_get(x_73, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_73, 1);
lean_inc(x_90);
lean_dec_ref(x_73);
x_91 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_69);
lean_ctor_set(x_91, 2, x_70);
lean_ctor_set_uint8(x_91, sizeof(void*)*3, x_68);
x_11 = x_89;
x_12 = x_91;
x_13 = lean_box(0);
goto block_15;
}
}
block_15:
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
block_44:
{
lean_object* x_18; 
x_18 = l_Lake_fetchFileTrace___redArg(x_1, x_3, x_8, x_16);
lean_dec_ref(x_8);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_18, 1);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_20, 1, x_22);
lean_ctor_set(x_18, 0, x_24);
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get_uint8(x_20, sizeof(void*)*3);
x_28 = lean_ctor_get(x_20, 2);
lean_inc(x_28);
lean_inc(x_26);
lean_dec(x_20);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_25);
lean_ctor_set(x_30, 2, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*3, x_27);
lean_ctor_set(x_18, 1, x_30);
lean_ctor_set(x_18, 0, x_29);
return x_18;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_18, 1);
x_32 = lean_ctor_get(x_18, 0);
lean_inc(x_31);
lean_inc(x_32);
lean_dec(x_18);
x_33 = lean_ctor_get(x_31, 0);
lean_inc_ref(x_33);
x_34 = lean_ctor_get_uint8(x_31, sizeof(void*)*3);
x_35 = lean_ctor_get(x_31, 2);
lean_inc(x_35);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 lean_ctor_release(x_31, 2);
 x_36 = x_31;
} else {
 lean_dec_ref(x_31);
 x_36 = lean_box(0);
}
x_37 = lean_box(0);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 3, 1);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_32);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set_uint8(x_38, sizeof(void*)*3, x_34);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_18);
if (x_40 == 0)
{
return x_18;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_18, 0);
x_42 = lean_ctor_get(x_18, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_18);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at_____private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_instBEq_beq___at_____private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at_____private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lake_MTime_checkUpToDate___at_____private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__1(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__4___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__4___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
x_14 = l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__4(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
x_12 = l_Lake_buildFileUnlessUpToDate_x27(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
static lean_object* _init_l_Lake_Cache_saveArtifact___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("artifacts", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_Cache_saveArtifact___closed__1() {
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
static lean_object* _init_l_Lake_Cache_saveArtifact___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Cache_saveArtifact___closed__1;
x_2 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6) {
_start:
{
if (x_4 == 0)
{
lean_object* x_8; 
x_8 = l_IO_FS_readBinFile(x_2);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_23; lean_object* x_24; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_10 = x_8;
} else {
 lean_dec_ref(x_8);
 x_10 = lean_box(0);
}
x_11 = lean_byte_array_hash(x_9);
lean_inc_ref(x_3);
x_12 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set_uint64(x_12, sizeof(void*)*1, x_11);
x_34 = l_Lake_Cache_saveArtifact___closed__0;
x_35 = l_System_FilePath_join(x_1, x_34);
x_52 = lean_string_utf8_byte_size(x_3);
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_nat_dec_eq(x_52, x_53);
lean_dec(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = l_Lake_Hash_hex(x_11);
x_56 = l_Lake_instToOutputJsonArtifact___lam__0___closed__0;
x_57 = lean_string_append(x_55, x_56);
x_58 = lean_string_append(x_57, x_3);
lean_dec_ref(x_3);
x_36 = x_58;
goto block_51;
}
else
{
lean_object* x_59; 
lean_dec_ref(x_3);
x_59 = l_Lake_Hash_hex(x_11);
x_36 = x_59;
goto block_51;
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_2);
lean_ctor_set(x_16, 3, x_14);
if (lean_is_scalar(x_10)) {
 x_17 = lean_alloc_ctor(0, 1, 0);
} else {
 x_17 = x_10;
}
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
block_22:
{
if (x_6 == 0)
{
x_13 = lean_box(0);
x_14 = x_21;
x_15 = x_20;
goto block_18;
}
else
{
lean_dec_ref(x_20);
lean_inc_ref(x_2);
x_13 = lean_box(0);
x_14 = x_21;
x_15 = x_2;
goto block_18;
}
}
block_33:
{
lean_object* x_25; 
lean_inc_ref(x_2);
x_25 = l_Lake_writeFileHash(x_2, x_11);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
lean_dec_ref(x_25);
x_26 = lean_io_metadata(x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc_ref(x_28);
lean_dec(x_27);
x_19 = lean_box(0);
x_20 = x_23;
x_21 = x_28;
goto block_22;
}
else
{
lean_object* x_29; 
lean_dec_ref(x_26);
x_29 = l_Lake_platformTrace___closed__6;
x_19 = lean_box(0);
x_20 = x_23;
x_21 = x_29;
goto block_22;
}
}
else
{
uint8_t x_30; 
lean_dec_ref(x_23);
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec_ref(x_2);
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_25, 0);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
block_51:
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lake_joinRelative(x_35, x_36);
lean_dec_ref(x_36);
x_38 = l_Lake_createParentDirs(x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
lean_dec_ref(x_38);
x_39 = l_IO_FS_writeBinFile(x_37, x_9);
lean_dec(x_9);
if (lean_obj_tag(x_39) == 0)
{
lean_dec_ref(x_39);
if (x_5 == 0)
{
x_23 = x_37;
x_24 = lean_box(0);
goto block_33;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = l_Lake_Cache_saveArtifact___closed__2;
x_41 = l_IO_setAccessRights(x_37, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_dec_ref(x_41);
x_23 = x_37;
x_24 = lean_box(0);
goto block_33;
}
else
{
uint8_t x_42; 
lean_dec_ref(x_37);
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec_ref(x_2);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
}
else
{
uint8_t x_45; 
lean_dec_ref(x_37);
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec_ref(x_2);
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
return x_39;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_39, 0);
lean_inc(x_46);
lean_dec(x_39);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec_ref(x_37);
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_2);
x_48 = !lean_is_exclusive(x_38);
if (x_48 == 0)
{
return x_38;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_38, 0);
lean_inc(x_49);
lean_dec(x_38);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
}
else
{
uint8_t x_60; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_60 = !lean_is_exclusive(x_8);
if (x_60 == 0)
{
return x_8;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_8, 0);
lean_inc(x_61);
lean_dec(x_8);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; 
x_63 = l_IO_FS_readFile(x_2);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint64_t x_67; uint64_t x_68; uint64_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
x_66 = l_String_crlfToLf(x_64);
lean_dec(x_64);
x_67 = l_Lake_platformTrace___closed__1;
x_68 = lean_string_hash(x_66);
x_69 = lean_uint64_mix_hash(x_67, x_68);
lean_inc_ref(x_3);
x_70 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_70, 0, x_3);
lean_ctor_set_uint64(x_70, sizeof(void*)*1, x_69);
x_81 = l_Lake_Cache_saveArtifact___closed__0;
x_82 = l_System_FilePath_join(x_1, x_81);
x_102 = lean_string_utf8_byte_size(x_3);
x_103 = lean_unsigned_to_nat(0u);
x_104 = lean_nat_dec_eq(x_102, x_103);
lean_dec(x_102);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = l_Lake_Hash_hex(x_69);
x_106 = l_Lake_instToOutputJsonArtifact___lam__0___closed__0;
x_107 = lean_string_append(x_105, x_106);
x_108 = lean_string_append(x_107, x_3);
lean_dec_ref(x_3);
x_83 = x_108;
goto block_101;
}
else
{
lean_object* x_109; 
lean_dec_ref(x_3);
x_109 = l_Lake_Hash_hex(x_69);
x_83 = x_109;
goto block_101;
}
block_76:
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_74, 0, x_70);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set(x_74, 2, x_2);
lean_ctor_set(x_74, 3, x_72);
if (lean_is_scalar(x_65)) {
 x_75 = lean_alloc_ctor(0, 1, 0);
} else {
 x_75 = x_65;
}
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
block_80:
{
if (x_6 == 0)
{
x_71 = lean_box(0);
x_72 = x_79;
x_73 = x_78;
goto block_76;
}
else
{
lean_dec_ref(x_78);
lean_inc_ref(x_2);
x_71 = lean_box(0);
x_72 = x_79;
x_73 = x_2;
goto block_76;
}
}
block_101:
{
lean_object* x_84; lean_object* x_85; 
x_84 = l_Lake_joinRelative(x_82, x_83);
lean_dec_ref(x_83);
x_85 = l_Lake_createParentDirs(x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; 
lean_dec_ref(x_85);
x_86 = l_IO_FS_writeFile(x_84, x_66);
lean_dec_ref(x_66);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; 
lean_dec_ref(x_86);
lean_inc_ref(x_2);
x_87 = l_Lake_writeFileHash(x_2, x_69);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
lean_dec_ref(x_87);
x_88 = lean_io_metadata(x_84);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec_ref(x_88);
x_90 = lean_ctor_get(x_89, 1);
lean_inc_ref(x_90);
lean_dec(x_89);
x_77 = lean_box(0);
x_78 = x_84;
x_79 = x_90;
goto block_80;
}
else
{
lean_object* x_91; 
lean_dec_ref(x_88);
x_91 = l_Lake_platformTrace___closed__6;
x_77 = lean_box(0);
x_78 = x_84;
x_79 = x_91;
goto block_80;
}
}
else
{
uint8_t x_92; 
lean_dec_ref(x_84);
lean_dec_ref(x_70);
lean_dec(x_65);
lean_dec_ref(x_2);
x_92 = !lean_is_exclusive(x_87);
if (x_92 == 0)
{
return x_87;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_87, 0);
lean_inc(x_93);
lean_dec(x_87);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec_ref(x_84);
lean_dec_ref(x_70);
lean_dec(x_65);
lean_dec_ref(x_2);
x_95 = !lean_is_exclusive(x_86);
if (x_95 == 0)
{
return x_86;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_86, 0);
lean_inc(x_96);
lean_dec(x_86);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec_ref(x_84);
lean_dec_ref(x_70);
lean_dec_ref(x_66);
lean_dec(x_65);
lean_dec_ref(x_2);
x_98 = !lean_is_exclusive(x_85);
if (x_98 == 0)
{
return x_85;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_85, 0);
lean_inc(x_99);
lean_dec(x_85);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
return x_100;
}
}
}
}
else
{
uint8_t x_110; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_110 = !lean_is_exclusive(x_63);
if (x_110 == 0)
{
return x_63;
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_63, 0);
lean_inc(x_111);
lean_dec(x_63);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_111);
return x_112;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_unbox(x_4);
x_9 = lean_unbox(x_5);
x_10 = lean_unbox(x_6);
x_11 = l_Lake_Cache_saveArtifact(x_1, x_2, x_3, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_box(x_3);
x_9 = lean_box(x_4);
x_10 = lean_box(x_5);
x_11 = lean_alloc_closure((void*)(l_Lake_Cache_saveArtifact___boxed), 7, 6);
lean_closure_set(x_11, 0, x_7);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_8);
lean_closure_set(x_11, 4, x_9);
lean_closure_set(x_11, 5, x_10);
x_12 = lean_apply_2(x_6, lean_box(0), x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, uint8_t x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec_ref(x_3);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_alloc_closure((void*)(l_Lake_cacheArtifact___redArg___lam__0___boxed), 1, 0);
x_14 = lean_box(x_6);
x_15 = lean_box(x_7);
x_16 = lean_box(x_8);
x_17 = lean_alloc_closure((void*)(l_Lake_cacheArtifact___redArg___lam__1___boxed), 7, 6);
lean_closure_set(x_17, 0, x_4);
lean_closure_set(x_17, 1, x_5);
lean_closure_set(x_17, 2, x_14);
lean_closure_set(x_17, 3, x_15);
lean_closure_set(x_17, 4, x_16);
lean_closure_set(x_17, 5, x_2);
x_18 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_13, x_1);
x_19 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_18, x_17);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, uint8_t x_8, uint8_t x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_dec_ref(x_4);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_alloc_closure((void*)(l_Lake_cacheArtifact___redArg___lam__0___boxed), 1, 0);
x_15 = lean_box(x_7);
x_16 = lean_box(x_8);
x_17 = lean_box(x_9);
x_18 = lean_alloc_closure((void*)(l_Lake_cacheArtifact___redArg___lam__1___boxed), 7, 6);
lean_closure_set(x_18, 0, x_5);
lean_closure_set(x_18, 1, x_6);
lean_closure_set(x_18, 2, x_15);
lean_closure_set(x_18, 3, x_16);
lean_closure_set(x_18, 4, x_17);
lean_closure_set(x_18, 5, x_3);
x_19 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_14, x_2);
x_20 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_19, x_18);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_cacheArtifact___redArg___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_unbox(x_3);
x_9 = lean_unbox(x_4);
x_10 = lean_unbox(x_5);
x_11 = l_Lake_cacheArtifact___redArg___lam__1(x_1, x_2, x_8, x_9, x_10, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_6);
x_10 = lean_unbox(x_7);
x_11 = lean_unbox(x_8);
x_12 = l_Lake_cacheArtifact___redArg(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_7);
x_11 = lean_unbox(x_8);
x_12 = lean_unbox(x_9);
x_13 = l_Lake_cacheArtifact(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_ResolveOutputs_ctorIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(0u);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_ResolveOutputs_ctorIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_ResolveOutputs_ctorIdx(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_getArtifacts_x3f___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("input '", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_getArtifacts_x3f___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' found in package artifact cache, but some output(s) have issues: ", 67, 67);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_24; uint8_t x_25; 
x_24 = l_Lake_instMonadWorkspaceJobM___closed__0;
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_28 = lean_ctor_get(x_24, 1);
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_26, 1);
x_31 = lean_ctor_get(x_26, 4);
lean_dec(x_31);
x_32 = lean_ctor_get(x_26, 3);
lean_dec(x_32);
x_33 = lean_ctor_get(x_26, 2);
lean_dec(x_33);
lean_inc(x_28);
lean_inc(x_30);
x_34 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_34, 0, x_30);
lean_closure_set(x_34, 1, x_28);
lean_inc(x_28);
lean_inc(x_30);
x_35 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_35, 0, x_30);
lean_closure_set(x_35, 1, x_28);
lean_inc_ref(x_34);
lean_inc(x_30);
x_36 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_36, 0, x_30);
lean_closure_set(x_36, 1, x_34);
lean_inc(x_30);
lean_inc_ref(x_29);
x_37 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_37, 0, x_29);
lean_closure_set(x_37, 1, x_30);
lean_closure_set(x_37, 2, x_28);
x_38 = l_Lake_EStateT_instFunctor___redArg(x_29);
x_39 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_39, 0, x_30);
lean_ctor_set(x_26, 4, x_35);
lean_ctor_set(x_26, 3, x_36);
lean_ctor_set(x_26, 2, x_37);
lean_ctor_set(x_26, 1, x_39);
lean_ctor_set(x_26, 0, x_38);
lean_ctor_set(x_24, 1, x_34);
x_40 = l_ReaderT_instMonad___redArg(x_24);
x_41 = l_ReaderT_instMonad___redArg(x_40);
x_42 = l_ReaderT_instMonad___redArg(x_41);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
lean_dec(x_45);
x_46 = lean_ctor_get(x_44, 0);
lean_inc_ref(x_46);
lean_dec_ref(x_44);
lean_inc_ref(x_46);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_47, 0, x_46);
x_48 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_48, 0, x_46);
lean_ctor_set(x_42, 1, x_48);
lean_ctor_set(x_42, 0, x_47);
x_49 = l_Lake_EquipT_instFunctor___redArg(x_42);
x_50 = l_Lake_instMonadWorkspaceJobM;
lean_inc_ref(x_5);
x_51 = l_Lake_Package_isArtifactCacheEnabled___redArg(x_49, x_50, x_5);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_52 = lean_apply_7(x_51, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
lean_dec_ref(x_52);
x_55 = !lean_is_exclusive(x_53);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_123; 
x_56 = lean_ctor_get(x_53, 0);
x_57 = l_Lake_Package_cacheScope(x_5);
lean_inc_ref(x_4);
x_123 = l_Lake_Cache_readOutputs_x3f(x_4, x_57, x_2, x_56);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec_ref(x_123);
lean_ctor_set(x_53, 0, x_125);
if (lean_obj_tag(x_124) == 0)
{
x_58 = x_6;
x_59 = x_7;
x_60 = x_8;
x_61 = x_9;
x_62 = x_10;
x_63 = x_53;
x_64 = lean_box(0);
goto block_122;
}
else
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_124);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_124, 0);
lean_inc_ref(x_1);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_128 = lean_apply_8(x_1, x_127, x_6, x_7, x_8, x_9, x_10, x_53, lean_box(0));
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; 
lean_free_object(x_124);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec_ref(x_128);
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
lean_dec_ref(x_129);
x_132 = !lean_is_exclusive(x_130);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; 
x_133 = lean_ctor_get(x_130, 0);
x_134 = l_Lake_getArtifacts_x3f___redArg___closed__0;
x_135 = l_Lake_Hash_hex(x_2);
x_136 = lean_unsigned_to_nat(7u);
x_137 = lean_unsigned_to_nat(0u);
x_138 = lean_string_utf8_byte_size(x_135);
lean_inc_ref(x_135);
x_139 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_139, 0, x_135);
lean_ctor_set(x_139, 1, x_137);
lean_ctor_set(x_139, 2, x_138);
x_140 = l_Substring_nextn(x_139, x_136, x_137);
lean_dec_ref(x_139);
x_141 = lean_string_utf8_extract(x_135, x_137, x_140);
lean_dec(x_140);
lean_dec_ref(x_135);
x_142 = lean_string_append(x_134, x_141);
lean_dec_ref(x_141);
x_143 = l_Lake_getArtifacts_x3f___redArg___closed__1;
x_144 = lean_string_append(x_142, x_143);
x_145 = lean_string_append(x_144, x_131);
lean_dec(x_131);
x_146 = 2;
x_147 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set_uint8(x_147, sizeof(void*)*1, x_146);
x_148 = lean_array_push(x_133, x_147);
lean_ctor_set(x_130, 0, x_148);
x_58 = x_6;
x_59 = x_7;
x_60 = x_8;
x_61 = x_9;
x_62 = x_10;
x_63 = x_130;
x_64 = lean_box(0);
goto block_122;
}
else
{
lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_149 = lean_ctor_get(x_130, 0);
x_150 = lean_ctor_get_uint8(x_130, sizeof(void*)*3);
x_151 = lean_ctor_get(x_130, 1);
x_152 = lean_ctor_get(x_130, 2);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_149);
lean_dec(x_130);
x_153 = l_Lake_getArtifacts_x3f___redArg___closed__0;
x_154 = l_Lake_Hash_hex(x_2);
x_155 = lean_unsigned_to_nat(7u);
x_156 = lean_unsigned_to_nat(0u);
x_157 = lean_string_utf8_byte_size(x_154);
lean_inc_ref(x_154);
x_158 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_158, 0, x_154);
lean_ctor_set(x_158, 1, x_156);
lean_ctor_set(x_158, 2, x_157);
x_159 = l_Substring_nextn(x_158, x_155, x_156);
lean_dec_ref(x_158);
x_160 = lean_string_utf8_extract(x_154, x_156, x_159);
lean_dec(x_159);
lean_dec_ref(x_154);
x_161 = lean_string_append(x_153, x_160);
lean_dec_ref(x_160);
x_162 = l_Lake_getArtifacts_x3f___redArg___closed__1;
x_163 = lean_string_append(x_161, x_162);
x_164 = lean_string_append(x_163, x_131);
lean_dec(x_131);
x_165 = 2;
x_166 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set_uint8(x_166, sizeof(void*)*1, x_165);
x_167 = lean_array_push(x_149, x_166);
x_168 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_151);
lean_ctor_set(x_168, 2, x_152);
lean_ctor_set_uint8(x_168, sizeof(void*)*3, x_150);
x_58 = x_6;
x_59 = x_7;
x_60 = x_8;
x_61 = x_9;
x_62 = x_10;
x_63 = x_168;
x_64 = lean_box(0);
goto block_122;
}
}
else
{
uint8_t x_169; 
lean_dec_ref(x_57);
lean_dec(x_54);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_169 = !lean_is_exclusive(x_128);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_ctor_get(x_128, 0);
lean_dec(x_170);
x_171 = lean_ctor_get(x_129, 0);
lean_inc(x_171);
lean_dec_ref(x_129);
lean_ctor_set(x_124, 0, x_171);
lean_ctor_set(x_128, 0, x_124);
return x_128;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_128, 1);
lean_inc(x_172);
lean_dec(x_128);
x_173 = lean_ctor_get(x_129, 0);
lean_inc(x_173);
lean_dec_ref(x_129);
lean_ctor_set(x_124, 0, x_173);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_124);
lean_ctor_set(x_174, 1, x_172);
return x_174;
}
}
}
else
{
uint8_t x_175; 
lean_free_object(x_124);
lean_dec_ref(x_57);
lean_dec(x_54);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_175 = !lean_is_exclusive(x_128);
if (x_175 == 0)
{
return x_128;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_128, 0);
x_177 = lean_ctor_get(x_128, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_128);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
else
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_124, 0);
lean_inc(x_179);
lean_dec(x_124);
lean_inc_ref(x_1);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_180 = lean_apply_8(x_1, x_179, x_6, x_7, x_8, x_9, x_10, x_53, lean_box(0));
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec_ref(x_180);
x_183 = lean_ctor_get(x_181, 0);
lean_inc(x_183);
lean_dec_ref(x_181);
x_184 = lean_ctor_get(x_182, 0);
lean_inc_ref(x_184);
x_185 = lean_ctor_get_uint8(x_182, sizeof(void*)*3);
x_186 = lean_ctor_get(x_182, 1);
lean_inc_ref(x_186);
x_187 = lean_ctor_get(x_182, 2);
lean_inc(x_187);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 lean_ctor_release(x_182, 2);
 x_188 = x_182;
} else {
 lean_dec_ref(x_182);
 x_188 = lean_box(0);
}
x_189 = l_Lake_getArtifacts_x3f___redArg___closed__0;
x_190 = l_Lake_Hash_hex(x_2);
x_191 = lean_unsigned_to_nat(7u);
x_192 = lean_unsigned_to_nat(0u);
x_193 = lean_string_utf8_byte_size(x_190);
lean_inc_ref(x_190);
x_194 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_194, 0, x_190);
lean_ctor_set(x_194, 1, x_192);
lean_ctor_set(x_194, 2, x_193);
x_195 = l_Substring_nextn(x_194, x_191, x_192);
lean_dec_ref(x_194);
x_196 = lean_string_utf8_extract(x_190, x_192, x_195);
lean_dec(x_195);
lean_dec_ref(x_190);
x_197 = lean_string_append(x_189, x_196);
lean_dec_ref(x_196);
x_198 = l_Lake_getArtifacts_x3f___redArg___closed__1;
x_199 = lean_string_append(x_197, x_198);
x_200 = lean_string_append(x_199, x_183);
lean_dec(x_183);
x_201 = 2;
x_202 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set_uint8(x_202, sizeof(void*)*1, x_201);
x_203 = lean_array_push(x_184, x_202);
if (lean_is_scalar(x_188)) {
 x_204 = lean_alloc_ctor(0, 3, 1);
} else {
 x_204 = x_188;
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_186);
lean_ctor_set(x_204, 2, x_187);
lean_ctor_set_uint8(x_204, sizeof(void*)*3, x_185);
x_58 = x_6;
x_59 = x_7;
x_60 = x_8;
x_61 = x_9;
x_62 = x_10;
x_63 = x_204;
x_64 = lean_box(0);
goto block_122;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec_ref(x_57);
lean_dec(x_54);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_205 = lean_ctor_get(x_180, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_206 = x_180;
} else {
 lean_dec_ref(x_180);
 x_206 = lean_box(0);
}
x_207 = lean_ctor_get(x_181, 0);
lean_inc(x_207);
lean_dec_ref(x_181);
x_208 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_208, 0, x_207);
if (lean_is_scalar(x_206)) {
 x_209 = lean_alloc_ctor(0, 2, 0);
} else {
 x_209 = x_206;
}
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_205);
return x_209;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec_ref(x_57);
lean_dec(x_54);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_210 = lean_ctor_get(x_180, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_180, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_212 = x_180;
} else {
 lean_dec_ref(x_180);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_213, 1, x_211);
return x_213;
}
}
}
}
else
{
uint8_t x_214; 
lean_dec_ref(x_57);
lean_dec(x_54);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_214 = !lean_is_exclusive(x_123);
if (x_214 == 0)
{
lean_object* x_215; 
x_215 = lean_ctor_get(x_123, 1);
lean_ctor_set(x_53, 0, x_215);
lean_ctor_set(x_123, 1, x_53);
return x_123;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_123, 0);
x_217 = lean_ctor_get(x_123, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_123);
lean_ctor_set(x_53, 0, x_217);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_53);
return x_218;
}
}
block_122:
{
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_65; uint64_t x_66; lean_object* x_67; uint8_t x_68; 
x_65 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_65);
lean_dec_ref(x_3);
x_66 = lean_ctor_get_uint64(x_65, sizeof(void*)*3);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec_ref(x_65);
x_68 = lean_uint64_dec_eq(x_66, x_2);
if (x_68 == 0)
{
lean_dec(x_67);
lean_dec_ref(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec_ref(x_58);
lean_dec_ref(x_57);
lean_dec(x_54);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_13 = x_63;
x_14 = lean_box(0);
goto block_17;
}
else
{
if (lean_obj_tag(x_67) == 0)
{
lean_dec_ref(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec_ref(x_58);
lean_dec_ref(x_57);
lean_dec(x_54);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_13 = x_63;
x_14 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
lean_dec_ref(x_67);
lean_inc(x_69);
x_70 = lean_apply_8(x_1, x_69, x_58, x_59, x_60, x_61, x_62, x_63, lean_box(0));
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; 
lean_dec_ref(x_71);
lean_dec(x_69);
lean_dec_ref(x_57);
lean_dec(x_54);
lean_dec_ref(x_4);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec_ref(x_70);
x_13 = x_72;
x_14 = lean_box(0);
goto block_17;
}
else
{
uint8_t x_73; 
x_73 = lean_unbox(x_54);
lean_dec(x_54);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_69);
lean_dec_ref(x_57);
lean_dec_ref(x_4);
x_74 = lean_ctor_get(x_70, 1);
lean_inc(x_74);
lean_dec_ref(x_70);
x_75 = lean_ctor_get(x_71, 0);
lean_inc(x_75);
lean_dec_ref(x_71);
x_18 = x_75;
x_19 = x_74;
x_20 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_70);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_77 = lean_ctor_get(x_70, 1);
x_78 = lean_ctor_get(x_70, 0);
lean_dec(x_78);
x_79 = lean_ctor_get(x_71, 0);
lean_inc(x_79);
lean_dec_ref(x_71);
x_80 = lean_ctor_get(x_77, 0);
x_81 = lean_ctor_get_uint8(x_77, sizeof(void*)*3);
x_82 = lean_ctor_get(x_77, 1);
x_83 = lean_ctor_get(x_77, 2);
x_84 = l_Lake_Cache_writeOutputsCore(x_4, x_57, x_2, x_69);
lean_dec_ref(x_57);
if (lean_obj_tag(x_84) == 0)
{
lean_dec_ref(x_84);
lean_free_object(x_70);
x_18 = x_79;
x_19 = x_77;
x_20 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_85; 
lean_inc(x_83);
lean_inc_ref(x_82);
lean_inc_ref(x_80);
lean_dec(x_79);
x_85 = !lean_is_exclusive(x_77);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_86 = lean_ctor_get(x_77, 2);
lean_dec(x_86);
x_87 = lean_ctor_get(x_77, 1);
lean_dec(x_87);
x_88 = lean_ctor_get(x_77, 0);
lean_dec(x_88);
x_89 = lean_ctor_get(x_84, 0);
lean_inc(x_89);
lean_dec_ref(x_84);
x_90 = lean_io_error_to_string(x_89);
x_91 = 3;
x_92 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_91);
x_93 = lean_array_get_size(x_80);
x_94 = lean_array_push(x_80, x_92);
lean_ctor_set(x_77, 0, x_94);
lean_ctor_set_tag(x_70, 1);
lean_ctor_set(x_70, 0, x_93);
return x_70;
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_77);
x_95 = lean_ctor_get(x_84, 0);
lean_inc(x_95);
lean_dec_ref(x_84);
x_96 = lean_io_error_to_string(x_95);
x_97 = 3;
x_98 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set_uint8(x_98, sizeof(void*)*1, x_97);
x_99 = lean_array_get_size(x_80);
x_100 = lean_array_push(x_80, x_98);
x_101 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_82);
lean_ctor_set(x_101, 2, x_83);
lean_ctor_set_uint8(x_101, sizeof(void*)*3, x_81);
lean_ctor_set_tag(x_70, 1);
lean_ctor_set(x_70, 1, x_101);
lean_ctor_set(x_70, 0, x_99);
return x_70;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_102 = lean_ctor_get(x_70, 1);
lean_inc(x_102);
lean_dec(x_70);
x_103 = lean_ctor_get(x_71, 0);
lean_inc(x_103);
lean_dec_ref(x_71);
x_104 = lean_ctor_get(x_102, 0);
x_105 = lean_ctor_get_uint8(x_102, sizeof(void*)*3);
x_106 = lean_ctor_get(x_102, 1);
x_107 = lean_ctor_get(x_102, 2);
x_108 = l_Lake_Cache_writeOutputsCore(x_4, x_57, x_2, x_69);
lean_dec_ref(x_57);
if (lean_obj_tag(x_108) == 0)
{
lean_dec_ref(x_108);
x_18 = x_103;
x_19 = x_102;
x_20 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_inc(x_107);
lean_inc_ref(x_106);
lean_inc_ref(x_104);
lean_dec(x_103);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 lean_ctor_release(x_102, 2);
 x_109 = x_102;
} else {
 lean_dec_ref(x_102);
 x_109 = lean_box(0);
}
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
lean_dec_ref(x_108);
x_111 = lean_io_error_to_string(x_110);
x_112 = 3;
x_113 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set_uint8(x_113, sizeof(void*)*1, x_112);
x_114 = lean_array_get_size(x_104);
x_115 = lean_array_push(x_104, x_113);
if (lean_is_scalar(x_109)) {
 x_116 = lean_alloc_ctor(0, 3, 1);
} else {
 x_116 = x_109;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_106);
lean_ctor_set(x_116, 2, x_107);
lean_ctor_set_uint8(x_116, sizeof(void*)*3, x_105);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_69);
lean_dec_ref(x_57);
lean_dec(x_54);
lean_dec_ref(x_4);
x_118 = !lean_is_exclusive(x_70);
if (x_118 == 0)
{
return x_70;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_70, 0);
x_120 = lean_ctor_get(x_70, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_70);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
}
}
else
{
lean_dec_ref(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec_ref(x_58);
lean_dec_ref(x_57);
lean_dec(x_54);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_13 = x_63;
x_14 = lean_box(0);
goto block_17;
}
}
}
else
{
lean_object* x_219; uint8_t x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_264; 
x_219 = lean_ctor_get(x_53, 0);
x_220 = lean_ctor_get_uint8(x_53, sizeof(void*)*3);
x_221 = lean_ctor_get(x_53, 1);
x_222 = lean_ctor_get(x_53, 2);
lean_inc(x_222);
lean_inc(x_221);
lean_inc(x_219);
lean_dec(x_53);
x_223 = l_Lake_Package_cacheScope(x_5);
lean_inc_ref(x_4);
x_264 = l_Lake_Cache_readOutputs_x3f(x_4, x_223, x_2, x_219);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec_ref(x_264);
x_267 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_221);
lean_ctor_set(x_267, 2, x_222);
lean_ctor_set_uint8(x_267, sizeof(void*)*3, x_220);
if (lean_obj_tag(x_265) == 0)
{
x_224 = x_6;
x_225 = x_7;
x_226 = x_8;
x_227 = x_9;
x_228 = x_10;
x_229 = x_267;
x_230 = lean_box(0);
goto block_263;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_265, 0);
lean_inc(x_268);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 x_269 = x_265;
} else {
 lean_dec_ref(x_265);
 x_269 = lean_box(0);
}
lean_inc_ref(x_1);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_270 = lean_apply_8(x_1, x_268, x_6, x_7, x_8, x_9, x_10, x_267, lean_box(0));
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; 
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_269);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
lean_dec_ref(x_270);
x_273 = lean_ctor_get(x_271, 0);
lean_inc(x_273);
lean_dec_ref(x_271);
x_274 = lean_ctor_get(x_272, 0);
lean_inc_ref(x_274);
x_275 = lean_ctor_get_uint8(x_272, sizeof(void*)*3);
x_276 = lean_ctor_get(x_272, 1);
lean_inc_ref(x_276);
x_277 = lean_ctor_get(x_272, 2);
lean_inc(x_277);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 lean_ctor_release(x_272, 2);
 x_278 = x_272;
} else {
 lean_dec_ref(x_272);
 x_278 = lean_box(0);
}
x_279 = l_Lake_getArtifacts_x3f___redArg___closed__0;
x_280 = l_Lake_Hash_hex(x_2);
x_281 = lean_unsigned_to_nat(7u);
x_282 = lean_unsigned_to_nat(0u);
x_283 = lean_string_utf8_byte_size(x_280);
lean_inc_ref(x_280);
x_284 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_284, 0, x_280);
lean_ctor_set(x_284, 1, x_282);
lean_ctor_set(x_284, 2, x_283);
x_285 = l_Substring_nextn(x_284, x_281, x_282);
lean_dec_ref(x_284);
x_286 = lean_string_utf8_extract(x_280, x_282, x_285);
lean_dec(x_285);
lean_dec_ref(x_280);
x_287 = lean_string_append(x_279, x_286);
lean_dec_ref(x_286);
x_288 = l_Lake_getArtifacts_x3f___redArg___closed__1;
x_289 = lean_string_append(x_287, x_288);
x_290 = lean_string_append(x_289, x_273);
lean_dec(x_273);
x_291 = 2;
x_292 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set_uint8(x_292, sizeof(void*)*1, x_291);
x_293 = lean_array_push(x_274, x_292);
if (lean_is_scalar(x_278)) {
 x_294 = lean_alloc_ctor(0, 3, 1);
} else {
 x_294 = x_278;
}
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_276);
lean_ctor_set(x_294, 2, x_277);
lean_ctor_set_uint8(x_294, sizeof(void*)*3, x_275);
x_224 = x_6;
x_225 = x_7;
x_226 = x_8;
x_227 = x_9;
x_228 = x_10;
x_229 = x_294;
x_230 = lean_box(0);
goto block_263;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec_ref(x_223);
lean_dec(x_54);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_295 = lean_ctor_get(x_270, 1);
lean_inc(x_295);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_296 = x_270;
} else {
 lean_dec_ref(x_270);
 x_296 = lean_box(0);
}
x_297 = lean_ctor_get(x_271, 0);
lean_inc(x_297);
lean_dec_ref(x_271);
if (lean_is_scalar(x_269)) {
 x_298 = lean_alloc_ctor(1, 1, 0);
} else {
 x_298 = x_269;
}
lean_ctor_set(x_298, 0, x_297);
if (lean_is_scalar(x_296)) {
 x_299 = lean_alloc_ctor(0, 2, 0);
} else {
 x_299 = x_296;
}
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_295);
return x_299;
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
lean_dec(x_269);
lean_dec_ref(x_223);
lean_dec(x_54);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_300 = lean_ctor_get(x_270, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_270, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_302 = x_270;
} else {
 lean_dec_ref(x_270);
 x_302 = lean_box(0);
}
if (lean_is_scalar(x_302)) {
 x_303 = lean_alloc_ctor(1, 2, 0);
} else {
 x_303 = x_302;
}
lean_ctor_set(x_303, 0, x_300);
lean_ctor_set(x_303, 1, x_301);
return x_303;
}
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
lean_dec_ref(x_223);
lean_dec(x_54);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_304 = lean_ctor_get(x_264, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_264, 1);
lean_inc(x_305);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 x_306 = x_264;
} else {
 lean_dec_ref(x_264);
 x_306 = lean_box(0);
}
x_307 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_307, 0, x_305);
lean_ctor_set(x_307, 1, x_221);
lean_ctor_set(x_307, 2, x_222);
lean_ctor_set_uint8(x_307, sizeof(void*)*3, x_220);
if (lean_is_scalar(x_306)) {
 x_308 = lean_alloc_ctor(1, 2, 0);
} else {
 x_308 = x_306;
}
lean_ctor_set(x_308, 0, x_304);
lean_ctor_set(x_308, 1, x_307);
return x_308;
}
block_263:
{
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_231; uint64_t x_232; lean_object* x_233; uint8_t x_234; 
x_231 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_231);
lean_dec_ref(x_3);
x_232 = lean_ctor_get_uint64(x_231, sizeof(void*)*3);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
lean_dec_ref(x_231);
x_234 = lean_uint64_dec_eq(x_232, x_2);
if (x_234 == 0)
{
lean_dec(x_233);
lean_dec_ref(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec_ref(x_224);
lean_dec_ref(x_223);
lean_dec(x_54);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_13 = x_229;
x_14 = lean_box(0);
goto block_17;
}
else
{
if (lean_obj_tag(x_233) == 0)
{
lean_dec_ref(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec_ref(x_224);
lean_dec_ref(x_223);
lean_dec(x_54);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_13 = x_229;
x_14 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_235; lean_object* x_236; 
x_235 = lean_ctor_get(x_233, 0);
lean_inc(x_235);
lean_dec_ref(x_233);
lean_inc(x_235);
x_236 = lean_apply_8(x_1, x_235, x_224, x_225, x_226, x_227, x_228, x_229, lean_box(0));
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; 
lean_dec_ref(x_237);
lean_dec(x_235);
lean_dec_ref(x_223);
lean_dec(x_54);
lean_dec_ref(x_4);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
lean_dec_ref(x_236);
x_13 = x_238;
x_14 = lean_box(0);
goto block_17;
}
else
{
uint8_t x_239; 
x_239 = lean_unbox(x_54);
lean_dec(x_54);
if (x_239 == 0)
{
lean_object* x_240; lean_object* x_241; 
lean_dec(x_235);
lean_dec_ref(x_223);
lean_dec_ref(x_4);
x_240 = lean_ctor_get(x_236, 1);
lean_inc(x_240);
lean_dec_ref(x_236);
x_241 = lean_ctor_get(x_237, 0);
lean_inc(x_241);
lean_dec_ref(x_237);
x_18 = x_241;
x_19 = x_240;
x_20 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
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
x_244 = lean_ctor_get(x_237, 0);
lean_inc(x_244);
lean_dec_ref(x_237);
x_245 = lean_ctor_get(x_242, 0);
x_246 = lean_ctor_get_uint8(x_242, sizeof(void*)*3);
x_247 = lean_ctor_get(x_242, 1);
x_248 = lean_ctor_get(x_242, 2);
x_249 = l_Lake_Cache_writeOutputsCore(x_4, x_223, x_2, x_235);
lean_dec_ref(x_223);
if (lean_obj_tag(x_249) == 0)
{
lean_dec_ref(x_249);
lean_dec(x_243);
x_18 = x_244;
x_19 = x_242;
x_20 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_inc(x_248);
lean_inc_ref(x_247);
lean_inc_ref(x_245);
lean_dec(x_244);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 lean_ctor_release(x_242, 2);
 x_250 = x_242;
} else {
 lean_dec_ref(x_242);
 x_250 = lean_box(0);
}
x_251 = lean_ctor_get(x_249, 0);
lean_inc(x_251);
lean_dec_ref(x_249);
x_252 = lean_io_error_to_string(x_251);
x_253 = 3;
x_254 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set_uint8(x_254, sizeof(void*)*1, x_253);
x_255 = lean_array_get_size(x_245);
x_256 = lean_array_push(x_245, x_254);
if (lean_is_scalar(x_250)) {
 x_257 = lean_alloc_ctor(0, 3, 1);
} else {
 x_257 = x_250;
}
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_247);
lean_ctor_set(x_257, 2, x_248);
lean_ctor_set_uint8(x_257, sizeof(void*)*3, x_246);
if (lean_is_scalar(x_243)) {
 x_258 = lean_alloc_ctor(1, 2, 0);
} else {
 x_258 = x_243;
 lean_ctor_set_tag(x_258, 1);
}
lean_ctor_set(x_258, 0, x_255);
lean_ctor_set(x_258, 1, x_257);
return x_258;
}
}
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_235);
lean_dec_ref(x_223);
lean_dec(x_54);
lean_dec_ref(x_4);
x_259 = lean_ctor_get(x_236, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_236, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_261 = x_236;
} else {
 lean_dec_ref(x_236);
 x_261 = lean_box(0);
}
if (lean_is_scalar(x_261)) {
 x_262 = lean_alloc_ctor(1, 2, 0);
} else {
 x_262 = x_261;
}
lean_ctor_set(x_262, 0, x_259);
lean_ctor_set(x_262, 1, x_260);
return x_262;
}
}
}
}
else
{
lean_dec_ref(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec_ref(x_224);
lean_dec_ref(x_223);
lean_dec(x_54);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_13 = x_229;
x_14 = lean_box(0);
goto block_17;
}
}
}
}
else
{
uint8_t x_309; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_309 = !lean_is_exclusive(x_52);
if (x_309 == 0)
{
return x_52;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_310 = lean_ctor_get(x_52, 0);
x_311 = lean_ctor_get(x_52, 1);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_52);
x_312 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_312, 0, x_310);
lean_ctor_set(x_312, 1, x_311);
return x_312;
}
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_313 = lean_ctor_get(x_42, 0);
lean_inc(x_313);
lean_dec(x_42);
x_314 = lean_ctor_get(x_313, 0);
lean_inc_ref(x_314);
lean_dec_ref(x_313);
lean_inc_ref(x_314);
x_315 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_315, 0, x_314);
x_316 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_316, 0, x_314);
x_317 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_317, 0, x_315);
lean_ctor_set(x_317, 1, x_316);
x_318 = l_Lake_EquipT_instFunctor___redArg(x_317);
x_319 = l_Lake_instMonadWorkspaceJobM;
lean_inc_ref(x_5);
x_320 = l_Lake_Package_isArtifactCacheEnabled___redArg(x_318, x_319, x_5);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_321 = lean_apply_7(x_320, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; uint8_t x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_370; 
x_322 = lean_ctor_get(x_321, 1);
lean_inc(x_322);
x_323 = lean_ctor_get(x_321, 0);
lean_inc(x_323);
lean_dec_ref(x_321);
x_324 = lean_ctor_get(x_322, 0);
lean_inc_ref(x_324);
x_325 = lean_ctor_get_uint8(x_322, sizeof(void*)*3);
x_326 = lean_ctor_get(x_322, 1);
lean_inc_ref(x_326);
x_327 = lean_ctor_get(x_322, 2);
lean_inc(x_327);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 lean_ctor_release(x_322, 1);
 lean_ctor_release(x_322, 2);
 x_328 = x_322;
} else {
 lean_dec_ref(x_322);
 x_328 = lean_box(0);
}
x_329 = l_Lake_Package_cacheScope(x_5);
lean_inc_ref(x_4);
x_370 = l_Lake_Cache_readOutputs_x3f(x_4, x_329, x_2, x_324);
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_370, 1);
lean_inc(x_372);
lean_dec_ref(x_370);
if (lean_is_scalar(x_328)) {
 x_373 = lean_alloc_ctor(0, 3, 1);
} else {
 x_373 = x_328;
}
lean_ctor_set(x_373, 0, x_372);
lean_ctor_set(x_373, 1, x_326);
lean_ctor_set(x_373, 2, x_327);
lean_ctor_set_uint8(x_373, sizeof(void*)*3, x_325);
if (lean_obj_tag(x_371) == 0)
{
x_330 = x_6;
x_331 = x_7;
x_332 = x_8;
x_333 = x_9;
x_334 = x_10;
x_335 = x_373;
x_336 = lean_box(0);
goto block_369;
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_374 = lean_ctor_get(x_371, 0);
lean_inc(x_374);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 x_375 = x_371;
} else {
 lean_dec_ref(x_371);
 x_375 = lean_box(0);
}
lean_inc_ref(x_1);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_376 = lean_apply_8(x_1, x_374, x_6, x_7, x_8, x_9, x_10, x_373, lean_box(0));
if (lean_obj_tag(x_376) == 0)
{
lean_object* x_377; 
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; uint8_t x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
lean_dec(x_375);
x_378 = lean_ctor_get(x_376, 1);
lean_inc(x_378);
lean_dec_ref(x_376);
x_379 = lean_ctor_get(x_377, 0);
lean_inc(x_379);
lean_dec_ref(x_377);
x_380 = lean_ctor_get(x_378, 0);
lean_inc_ref(x_380);
x_381 = lean_ctor_get_uint8(x_378, sizeof(void*)*3);
x_382 = lean_ctor_get(x_378, 1);
lean_inc_ref(x_382);
x_383 = lean_ctor_get(x_378, 2);
lean_inc(x_383);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 lean_ctor_release(x_378, 2);
 x_384 = x_378;
} else {
 lean_dec_ref(x_378);
 x_384 = lean_box(0);
}
x_385 = l_Lake_getArtifacts_x3f___redArg___closed__0;
x_386 = l_Lake_Hash_hex(x_2);
x_387 = lean_unsigned_to_nat(7u);
x_388 = lean_unsigned_to_nat(0u);
x_389 = lean_string_utf8_byte_size(x_386);
lean_inc_ref(x_386);
x_390 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_390, 0, x_386);
lean_ctor_set(x_390, 1, x_388);
lean_ctor_set(x_390, 2, x_389);
x_391 = l_Substring_nextn(x_390, x_387, x_388);
lean_dec_ref(x_390);
x_392 = lean_string_utf8_extract(x_386, x_388, x_391);
lean_dec(x_391);
lean_dec_ref(x_386);
x_393 = lean_string_append(x_385, x_392);
lean_dec_ref(x_392);
x_394 = l_Lake_getArtifacts_x3f___redArg___closed__1;
x_395 = lean_string_append(x_393, x_394);
x_396 = lean_string_append(x_395, x_379);
lean_dec(x_379);
x_397 = 2;
x_398 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_398, 0, x_396);
lean_ctor_set_uint8(x_398, sizeof(void*)*1, x_397);
x_399 = lean_array_push(x_380, x_398);
if (lean_is_scalar(x_384)) {
 x_400 = lean_alloc_ctor(0, 3, 1);
} else {
 x_400 = x_384;
}
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_382);
lean_ctor_set(x_400, 2, x_383);
lean_ctor_set_uint8(x_400, sizeof(void*)*3, x_381);
x_330 = x_6;
x_331 = x_7;
x_332 = x_8;
x_333 = x_9;
x_334 = x_10;
x_335 = x_400;
x_336 = lean_box(0);
goto block_369;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
lean_dec_ref(x_329);
lean_dec(x_323);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_401 = lean_ctor_get(x_376, 1);
lean_inc(x_401);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 x_402 = x_376;
} else {
 lean_dec_ref(x_376);
 x_402 = lean_box(0);
}
x_403 = lean_ctor_get(x_377, 0);
lean_inc(x_403);
lean_dec_ref(x_377);
if (lean_is_scalar(x_375)) {
 x_404 = lean_alloc_ctor(1, 1, 0);
} else {
 x_404 = x_375;
}
lean_ctor_set(x_404, 0, x_403);
if (lean_is_scalar(x_402)) {
 x_405 = lean_alloc_ctor(0, 2, 0);
} else {
 x_405 = x_402;
}
lean_ctor_set(x_405, 0, x_404);
lean_ctor_set(x_405, 1, x_401);
return x_405;
}
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
lean_dec(x_375);
lean_dec_ref(x_329);
lean_dec(x_323);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_406 = lean_ctor_get(x_376, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_376, 1);
lean_inc(x_407);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 x_408 = x_376;
} else {
 lean_dec_ref(x_376);
 x_408 = lean_box(0);
}
if (lean_is_scalar(x_408)) {
 x_409 = lean_alloc_ctor(1, 2, 0);
} else {
 x_409 = x_408;
}
lean_ctor_set(x_409, 0, x_406);
lean_ctor_set(x_409, 1, x_407);
return x_409;
}
}
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
lean_dec_ref(x_329);
lean_dec(x_323);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_410 = lean_ctor_get(x_370, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_370, 1);
lean_inc(x_411);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 x_412 = x_370;
} else {
 lean_dec_ref(x_370);
 x_412 = lean_box(0);
}
if (lean_is_scalar(x_328)) {
 x_413 = lean_alloc_ctor(0, 3, 1);
} else {
 x_413 = x_328;
}
lean_ctor_set(x_413, 0, x_411);
lean_ctor_set(x_413, 1, x_326);
lean_ctor_set(x_413, 2, x_327);
lean_ctor_set_uint8(x_413, sizeof(void*)*3, x_325);
if (lean_is_scalar(x_412)) {
 x_414 = lean_alloc_ctor(1, 2, 0);
} else {
 x_414 = x_412;
}
lean_ctor_set(x_414, 0, x_410);
lean_ctor_set(x_414, 1, x_413);
return x_414;
}
block_369:
{
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_337; uint64_t x_338; lean_object* x_339; uint8_t x_340; 
x_337 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_337);
lean_dec_ref(x_3);
x_338 = lean_ctor_get_uint64(x_337, sizeof(void*)*3);
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
lean_dec_ref(x_337);
x_340 = lean_uint64_dec_eq(x_338, x_2);
if (x_340 == 0)
{
lean_dec(x_339);
lean_dec_ref(x_334);
lean_dec(x_333);
lean_dec(x_332);
lean_dec(x_331);
lean_dec_ref(x_330);
lean_dec_ref(x_329);
lean_dec(x_323);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_13 = x_335;
x_14 = lean_box(0);
goto block_17;
}
else
{
if (lean_obj_tag(x_339) == 0)
{
lean_dec_ref(x_334);
lean_dec(x_333);
lean_dec(x_332);
lean_dec(x_331);
lean_dec_ref(x_330);
lean_dec_ref(x_329);
lean_dec(x_323);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_13 = x_335;
x_14 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_341; lean_object* x_342; 
x_341 = lean_ctor_get(x_339, 0);
lean_inc(x_341);
lean_dec_ref(x_339);
lean_inc(x_341);
x_342 = lean_apply_8(x_1, x_341, x_330, x_331, x_332, x_333, x_334, x_335, lean_box(0));
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; 
lean_dec_ref(x_343);
lean_dec(x_341);
lean_dec_ref(x_329);
lean_dec(x_323);
lean_dec_ref(x_4);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec_ref(x_342);
x_13 = x_344;
x_14 = lean_box(0);
goto block_17;
}
else
{
uint8_t x_345; 
x_345 = lean_unbox(x_323);
lean_dec(x_323);
if (x_345 == 0)
{
lean_object* x_346; lean_object* x_347; 
lean_dec(x_341);
lean_dec_ref(x_329);
lean_dec_ref(x_4);
x_346 = lean_ctor_get(x_342, 1);
lean_inc(x_346);
lean_dec_ref(x_342);
x_347 = lean_ctor_get(x_343, 0);
lean_inc(x_347);
lean_dec_ref(x_343);
x_18 = x_347;
x_19 = x_346;
x_20 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_348 = lean_ctor_get(x_342, 1);
lean_inc(x_348);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_349 = x_342;
} else {
 lean_dec_ref(x_342);
 x_349 = lean_box(0);
}
x_350 = lean_ctor_get(x_343, 0);
lean_inc(x_350);
lean_dec_ref(x_343);
x_351 = lean_ctor_get(x_348, 0);
x_352 = lean_ctor_get_uint8(x_348, sizeof(void*)*3);
x_353 = lean_ctor_get(x_348, 1);
x_354 = lean_ctor_get(x_348, 2);
x_355 = l_Lake_Cache_writeOutputsCore(x_4, x_329, x_2, x_341);
lean_dec_ref(x_329);
if (lean_obj_tag(x_355) == 0)
{
lean_dec_ref(x_355);
lean_dec(x_349);
x_18 = x_350;
x_19 = x_348;
x_20 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
lean_inc(x_354);
lean_inc_ref(x_353);
lean_inc_ref(x_351);
lean_dec(x_350);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 lean_ctor_release(x_348, 2);
 x_356 = x_348;
} else {
 lean_dec_ref(x_348);
 x_356 = lean_box(0);
}
x_357 = lean_ctor_get(x_355, 0);
lean_inc(x_357);
lean_dec_ref(x_355);
x_358 = lean_io_error_to_string(x_357);
x_359 = 3;
x_360 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_360, 0, x_358);
lean_ctor_set_uint8(x_360, sizeof(void*)*1, x_359);
x_361 = lean_array_get_size(x_351);
x_362 = lean_array_push(x_351, x_360);
if (lean_is_scalar(x_356)) {
 x_363 = lean_alloc_ctor(0, 3, 1);
} else {
 x_363 = x_356;
}
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_353);
lean_ctor_set(x_363, 2, x_354);
lean_ctor_set_uint8(x_363, sizeof(void*)*3, x_352);
if (lean_is_scalar(x_349)) {
 x_364 = lean_alloc_ctor(1, 2, 0);
} else {
 x_364 = x_349;
 lean_ctor_set_tag(x_364, 1);
}
lean_ctor_set(x_364, 0, x_361);
lean_ctor_set(x_364, 1, x_363);
return x_364;
}
}
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
lean_dec(x_341);
lean_dec_ref(x_329);
lean_dec(x_323);
lean_dec_ref(x_4);
x_365 = lean_ctor_get(x_342, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_342, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_367 = x_342;
} else {
 lean_dec_ref(x_342);
 x_367 = lean_box(0);
}
if (lean_is_scalar(x_367)) {
 x_368 = lean_alloc_ctor(1, 2, 0);
} else {
 x_368 = x_367;
}
lean_ctor_set(x_368, 0, x_365);
lean_ctor_set(x_368, 1, x_366);
return x_368;
}
}
}
}
else
{
lean_dec_ref(x_334);
lean_dec(x_333);
lean_dec(x_332);
lean_dec(x_331);
lean_dec_ref(x_330);
lean_dec_ref(x_329);
lean_dec(x_323);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_13 = x_335;
x_14 = lean_box(0);
goto block_17;
}
}
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_415 = lean_ctor_get(x_321, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_321, 1);
lean_inc(x_416);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 x_417 = x_321;
} else {
 lean_dec_ref(x_321);
 x_417 = lean_box(0);
}
if (lean_is_scalar(x_417)) {
 x_418 = lean_alloc_ctor(1, 2, 0);
} else {
 x_418 = x_417;
}
lean_ctor_set(x_418, 0, x_415);
lean_ctor_set(x_418, 1, x_416);
return x_418;
}
}
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_419 = lean_ctor_get(x_24, 1);
x_420 = lean_ctor_get(x_26, 0);
x_421 = lean_ctor_get(x_26, 1);
lean_inc(x_421);
lean_inc(x_420);
lean_dec(x_26);
lean_inc(x_419);
lean_inc(x_421);
x_422 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_422, 0, x_421);
lean_closure_set(x_422, 1, x_419);
lean_inc(x_419);
lean_inc(x_421);
x_423 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_423, 0, x_421);
lean_closure_set(x_423, 1, x_419);
lean_inc_ref(x_422);
lean_inc(x_421);
x_424 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_424, 0, x_421);
lean_closure_set(x_424, 1, x_422);
lean_inc(x_421);
lean_inc_ref(x_420);
x_425 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_425, 0, x_420);
lean_closure_set(x_425, 1, x_421);
lean_closure_set(x_425, 2, x_419);
x_426 = l_Lake_EStateT_instFunctor___redArg(x_420);
x_427 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_427, 0, x_421);
x_428 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_428, 0, x_426);
lean_ctor_set(x_428, 1, x_427);
lean_ctor_set(x_428, 2, x_425);
lean_ctor_set(x_428, 3, x_424);
lean_ctor_set(x_428, 4, x_423);
lean_ctor_set(x_24, 1, x_422);
lean_ctor_set(x_24, 0, x_428);
x_429 = l_ReaderT_instMonad___redArg(x_24);
x_430 = l_ReaderT_instMonad___redArg(x_429);
x_431 = l_ReaderT_instMonad___redArg(x_430);
x_432 = lean_ctor_get(x_431, 0);
lean_inc_ref(x_432);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 x_433 = x_431;
} else {
 lean_dec_ref(x_431);
 x_433 = lean_box(0);
}
x_434 = lean_ctor_get(x_432, 0);
lean_inc_ref(x_434);
lean_dec_ref(x_432);
lean_inc_ref(x_434);
x_435 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_435, 0, x_434);
x_436 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_436, 0, x_434);
if (lean_is_scalar(x_433)) {
 x_437 = lean_alloc_ctor(0, 2, 0);
} else {
 x_437 = x_433;
}
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set(x_437, 1, x_436);
x_438 = l_Lake_EquipT_instFunctor___redArg(x_437);
x_439 = l_Lake_instMonadWorkspaceJobM;
lean_inc_ref(x_5);
x_440 = l_Lake_Package_isArtifactCacheEnabled___redArg(x_438, x_439, x_5);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_441 = lean_apply_7(x_440, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_441) == 0)
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; uint8_t x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_490; 
x_442 = lean_ctor_get(x_441, 1);
lean_inc(x_442);
x_443 = lean_ctor_get(x_441, 0);
lean_inc(x_443);
lean_dec_ref(x_441);
x_444 = lean_ctor_get(x_442, 0);
lean_inc_ref(x_444);
x_445 = lean_ctor_get_uint8(x_442, sizeof(void*)*3);
x_446 = lean_ctor_get(x_442, 1);
lean_inc_ref(x_446);
x_447 = lean_ctor_get(x_442, 2);
lean_inc(x_447);
if (lean_is_exclusive(x_442)) {
 lean_ctor_release(x_442, 0);
 lean_ctor_release(x_442, 1);
 lean_ctor_release(x_442, 2);
 x_448 = x_442;
} else {
 lean_dec_ref(x_442);
 x_448 = lean_box(0);
}
x_449 = l_Lake_Package_cacheScope(x_5);
lean_inc_ref(x_4);
x_490 = l_Lake_Cache_readOutputs_x3f(x_4, x_449, x_2, x_444);
if (lean_obj_tag(x_490) == 0)
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_491 = lean_ctor_get(x_490, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_490, 1);
lean_inc(x_492);
lean_dec_ref(x_490);
if (lean_is_scalar(x_448)) {
 x_493 = lean_alloc_ctor(0, 3, 1);
} else {
 x_493 = x_448;
}
lean_ctor_set(x_493, 0, x_492);
lean_ctor_set(x_493, 1, x_446);
lean_ctor_set(x_493, 2, x_447);
lean_ctor_set_uint8(x_493, sizeof(void*)*3, x_445);
if (lean_obj_tag(x_491) == 0)
{
x_450 = x_6;
x_451 = x_7;
x_452 = x_8;
x_453 = x_9;
x_454 = x_10;
x_455 = x_493;
x_456 = lean_box(0);
goto block_489;
}
else
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; 
x_494 = lean_ctor_get(x_491, 0);
lean_inc(x_494);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 x_495 = x_491;
} else {
 lean_dec_ref(x_491);
 x_495 = lean_box(0);
}
lean_inc_ref(x_1);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_496 = lean_apply_8(x_1, x_494, x_6, x_7, x_8, x_9, x_10, x_493, lean_box(0));
if (lean_obj_tag(x_496) == 0)
{
lean_object* x_497; 
x_497 = lean_ctor_get(x_496, 0);
lean_inc(x_497);
if (lean_obj_tag(x_497) == 0)
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; uint8_t x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; uint8_t x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; 
lean_dec(x_495);
x_498 = lean_ctor_get(x_496, 1);
lean_inc(x_498);
lean_dec_ref(x_496);
x_499 = lean_ctor_get(x_497, 0);
lean_inc(x_499);
lean_dec_ref(x_497);
x_500 = lean_ctor_get(x_498, 0);
lean_inc_ref(x_500);
x_501 = lean_ctor_get_uint8(x_498, sizeof(void*)*3);
x_502 = lean_ctor_get(x_498, 1);
lean_inc_ref(x_502);
x_503 = lean_ctor_get(x_498, 2);
lean_inc(x_503);
if (lean_is_exclusive(x_498)) {
 lean_ctor_release(x_498, 0);
 lean_ctor_release(x_498, 1);
 lean_ctor_release(x_498, 2);
 x_504 = x_498;
} else {
 lean_dec_ref(x_498);
 x_504 = lean_box(0);
}
x_505 = l_Lake_getArtifacts_x3f___redArg___closed__0;
x_506 = l_Lake_Hash_hex(x_2);
x_507 = lean_unsigned_to_nat(7u);
x_508 = lean_unsigned_to_nat(0u);
x_509 = lean_string_utf8_byte_size(x_506);
lean_inc_ref(x_506);
x_510 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_510, 0, x_506);
lean_ctor_set(x_510, 1, x_508);
lean_ctor_set(x_510, 2, x_509);
x_511 = l_Substring_nextn(x_510, x_507, x_508);
lean_dec_ref(x_510);
x_512 = lean_string_utf8_extract(x_506, x_508, x_511);
lean_dec(x_511);
lean_dec_ref(x_506);
x_513 = lean_string_append(x_505, x_512);
lean_dec_ref(x_512);
x_514 = l_Lake_getArtifacts_x3f___redArg___closed__1;
x_515 = lean_string_append(x_513, x_514);
x_516 = lean_string_append(x_515, x_499);
lean_dec(x_499);
x_517 = 2;
x_518 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_518, 0, x_516);
lean_ctor_set_uint8(x_518, sizeof(void*)*1, x_517);
x_519 = lean_array_push(x_500, x_518);
if (lean_is_scalar(x_504)) {
 x_520 = lean_alloc_ctor(0, 3, 1);
} else {
 x_520 = x_504;
}
lean_ctor_set(x_520, 0, x_519);
lean_ctor_set(x_520, 1, x_502);
lean_ctor_set(x_520, 2, x_503);
lean_ctor_set_uint8(x_520, sizeof(void*)*3, x_501);
x_450 = x_6;
x_451 = x_7;
x_452 = x_8;
x_453 = x_9;
x_454 = x_10;
x_455 = x_520;
x_456 = lean_box(0);
goto block_489;
}
else
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; 
lean_dec_ref(x_449);
lean_dec(x_443);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_521 = lean_ctor_get(x_496, 1);
lean_inc(x_521);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 lean_ctor_release(x_496, 1);
 x_522 = x_496;
} else {
 lean_dec_ref(x_496);
 x_522 = lean_box(0);
}
x_523 = lean_ctor_get(x_497, 0);
lean_inc(x_523);
lean_dec_ref(x_497);
if (lean_is_scalar(x_495)) {
 x_524 = lean_alloc_ctor(1, 1, 0);
} else {
 x_524 = x_495;
}
lean_ctor_set(x_524, 0, x_523);
if (lean_is_scalar(x_522)) {
 x_525 = lean_alloc_ctor(0, 2, 0);
} else {
 x_525 = x_522;
}
lean_ctor_set(x_525, 0, x_524);
lean_ctor_set(x_525, 1, x_521);
return x_525;
}
}
else
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; 
lean_dec(x_495);
lean_dec_ref(x_449);
lean_dec(x_443);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_526 = lean_ctor_get(x_496, 0);
lean_inc(x_526);
x_527 = lean_ctor_get(x_496, 1);
lean_inc(x_527);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 lean_ctor_release(x_496, 1);
 x_528 = x_496;
} else {
 lean_dec_ref(x_496);
 x_528 = lean_box(0);
}
if (lean_is_scalar(x_528)) {
 x_529 = lean_alloc_ctor(1, 2, 0);
} else {
 x_529 = x_528;
}
lean_ctor_set(x_529, 0, x_526);
lean_ctor_set(x_529, 1, x_527);
return x_529;
}
}
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; 
lean_dec_ref(x_449);
lean_dec(x_443);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_530 = lean_ctor_get(x_490, 0);
lean_inc(x_530);
x_531 = lean_ctor_get(x_490, 1);
lean_inc(x_531);
if (lean_is_exclusive(x_490)) {
 lean_ctor_release(x_490, 0);
 lean_ctor_release(x_490, 1);
 x_532 = x_490;
} else {
 lean_dec_ref(x_490);
 x_532 = lean_box(0);
}
if (lean_is_scalar(x_448)) {
 x_533 = lean_alloc_ctor(0, 3, 1);
} else {
 x_533 = x_448;
}
lean_ctor_set(x_533, 0, x_531);
lean_ctor_set(x_533, 1, x_446);
lean_ctor_set(x_533, 2, x_447);
lean_ctor_set_uint8(x_533, sizeof(void*)*3, x_445);
if (lean_is_scalar(x_532)) {
 x_534 = lean_alloc_ctor(1, 2, 0);
} else {
 x_534 = x_532;
}
lean_ctor_set(x_534, 0, x_530);
lean_ctor_set(x_534, 1, x_533);
return x_534;
}
block_489:
{
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_457; uint64_t x_458; lean_object* x_459; uint8_t x_460; 
x_457 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_457);
lean_dec_ref(x_3);
x_458 = lean_ctor_get_uint64(x_457, sizeof(void*)*3);
x_459 = lean_ctor_get(x_457, 1);
lean_inc(x_459);
lean_dec_ref(x_457);
x_460 = lean_uint64_dec_eq(x_458, x_2);
if (x_460 == 0)
{
lean_dec(x_459);
lean_dec_ref(x_454);
lean_dec(x_453);
lean_dec(x_452);
lean_dec(x_451);
lean_dec_ref(x_450);
lean_dec_ref(x_449);
lean_dec(x_443);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_13 = x_455;
x_14 = lean_box(0);
goto block_17;
}
else
{
if (lean_obj_tag(x_459) == 0)
{
lean_dec_ref(x_454);
lean_dec(x_453);
lean_dec(x_452);
lean_dec(x_451);
lean_dec_ref(x_450);
lean_dec_ref(x_449);
lean_dec(x_443);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_13 = x_455;
x_14 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_461; lean_object* x_462; 
x_461 = lean_ctor_get(x_459, 0);
lean_inc(x_461);
lean_dec_ref(x_459);
lean_inc(x_461);
x_462 = lean_apply_8(x_1, x_461, x_450, x_451, x_452, x_453, x_454, x_455, lean_box(0));
if (lean_obj_tag(x_462) == 0)
{
lean_object* x_463; 
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
if (lean_obj_tag(x_463) == 0)
{
lean_object* x_464; 
lean_dec_ref(x_463);
lean_dec(x_461);
lean_dec_ref(x_449);
lean_dec(x_443);
lean_dec_ref(x_4);
x_464 = lean_ctor_get(x_462, 1);
lean_inc(x_464);
lean_dec_ref(x_462);
x_13 = x_464;
x_14 = lean_box(0);
goto block_17;
}
else
{
uint8_t x_465; 
x_465 = lean_unbox(x_443);
lean_dec(x_443);
if (x_465 == 0)
{
lean_object* x_466; lean_object* x_467; 
lean_dec(x_461);
lean_dec_ref(x_449);
lean_dec_ref(x_4);
x_466 = lean_ctor_get(x_462, 1);
lean_inc(x_466);
lean_dec_ref(x_462);
x_467 = lean_ctor_get(x_463, 0);
lean_inc(x_467);
lean_dec_ref(x_463);
x_18 = x_467;
x_19 = x_466;
x_20 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; uint8_t x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_468 = lean_ctor_get(x_462, 1);
lean_inc(x_468);
if (lean_is_exclusive(x_462)) {
 lean_ctor_release(x_462, 0);
 lean_ctor_release(x_462, 1);
 x_469 = x_462;
} else {
 lean_dec_ref(x_462);
 x_469 = lean_box(0);
}
x_470 = lean_ctor_get(x_463, 0);
lean_inc(x_470);
lean_dec_ref(x_463);
x_471 = lean_ctor_get(x_468, 0);
x_472 = lean_ctor_get_uint8(x_468, sizeof(void*)*3);
x_473 = lean_ctor_get(x_468, 1);
x_474 = lean_ctor_get(x_468, 2);
x_475 = l_Lake_Cache_writeOutputsCore(x_4, x_449, x_2, x_461);
lean_dec_ref(x_449);
if (lean_obj_tag(x_475) == 0)
{
lean_dec_ref(x_475);
lean_dec(x_469);
x_18 = x_470;
x_19 = x_468;
x_20 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; uint8_t x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; 
lean_inc(x_474);
lean_inc_ref(x_473);
lean_inc_ref(x_471);
lean_dec(x_470);
if (lean_is_exclusive(x_468)) {
 lean_ctor_release(x_468, 0);
 lean_ctor_release(x_468, 1);
 lean_ctor_release(x_468, 2);
 x_476 = x_468;
} else {
 lean_dec_ref(x_468);
 x_476 = lean_box(0);
}
x_477 = lean_ctor_get(x_475, 0);
lean_inc(x_477);
lean_dec_ref(x_475);
x_478 = lean_io_error_to_string(x_477);
x_479 = 3;
x_480 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_480, 0, x_478);
lean_ctor_set_uint8(x_480, sizeof(void*)*1, x_479);
x_481 = lean_array_get_size(x_471);
x_482 = lean_array_push(x_471, x_480);
if (lean_is_scalar(x_476)) {
 x_483 = lean_alloc_ctor(0, 3, 1);
} else {
 x_483 = x_476;
}
lean_ctor_set(x_483, 0, x_482);
lean_ctor_set(x_483, 1, x_473);
lean_ctor_set(x_483, 2, x_474);
lean_ctor_set_uint8(x_483, sizeof(void*)*3, x_472);
if (lean_is_scalar(x_469)) {
 x_484 = lean_alloc_ctor(1, 2, 0);
} else {
 x_484 = x_469;
 lean_ctor_set_tag(x_484, 1);
}
lean_ctor_set(x_484, 0, x_481);
lean_ctor_set(x_484, 1, x_483);
return x_484;
}
}
}
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
lean_dec(x_461);
lean_dec_ref(x_449);
lean_dec(x_443);
lean_dec_ref(x_4);
x_485 = lean_ctor_get(x_462, 0);
lean_inc(x_485);
x_486 = lean_ctor_get(x_462, 1);
lean_inc(x_486);
if (lean_is_exclusive(x_462)) {
 lean_ctor_release(x_462, 0);
 lean_ctor_release(x_462, 1);
 x_487 = x_462;
} else {
 lean_dec_ref(x_462);
 x_487 = lean_box(0);
}
if (lean_is_scalar(x_487)) {
 x_488 = lean_alloc_ctor(1, 2, 0);
} else {
 x_488 = x_487;
}
lean_ctor_set(x_488, 0, x_485);
lean_ctor_set(x_488, 1, x_486);
return x_488;
}
}
}
}
else
{
lean_dec_ref(x_454);
lean_dec(x_453);
lean_dec(x_452);
lean_dec(x_451);
lean_dec_ref(x_450);
lean_dec_ref(x_449);
lean_dec(x_443);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_13 = x_455;
x_14 = lean_box(0);
goto block_17;
}
}
}
else
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_535 = lean_ctor_get(x_441, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_441, 1);
lean_inc(x_536);
if (lean_is_exclusive(x_441)) {
 lean_ctor_release(x_441, 0);
 lean_ctor_release(x_441, 1);
 x_537 = x_441;
} else {
 lean_dec_ref(x_441);
 x_537 = lean_box(0);
}
if (lean_is_scalar(x_537)) {
 x_538 = lean_alloc_ctor(1, 2, 0);
} else {
 x_538 = x_537;
}
lean_ctor_set(x_538, 0, x_535);
lean_ctor_set(x_538, 1, x_536);
return x_538;
}
}
}
else
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; 
x_539 = lean_ctor_get(x_24, 0);
x_540 = lean_ctor_get(x_24, 1);
lean_inc(x_540);
lean_inc(x_539);
lean_dec(x_24);
x_541 = lean_ctor_get(x_539, 0);
lean_inc_ref(x_541);
x_542 = lean_ctor_get(x_539, 1);
lean_inc(x_542);
if (lean_is_exclusive(x_539)) {
 lean_ctor_release(x_539, 0);
 lean_ctor_release(x_539, 1);
 lean_ctor_release(x_539, 2);
 lean_ctor_release(x_539, 3);
 lean_ctor_release(x_539, 4);
 x_543 = x_539;
} else {
 lean_dec_ref(x_539);
 x_543 = lean_box(0);
}
lean_inc(x_540);
lean_inc(x_542);
x_544 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_544, 0, x_542);
lean_closure_set(x_544, 1, x_540);
lean_inc(x_540);
lean_inc(x_542);
x_545 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_545, 0, x_542);
lean_closure_set(x_545, 1, x_540);
lean_inc_ref(x_544);
lean_inc(x_542);
x_546 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_546, 0, x_542);
lean_closure_set(x_546, 1, x_544);
lean_inc(x_542);
lean_inc_ref(x_541);
x_547 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_547, 0, x_541);
lean_closure_set(x_547, 1, x_542);
lean_closure_set(x_547, 2, x_540);
x_548 = l_Lake_EStateT_instFunctor___redArg(x_541);
x_549 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_549, 0, x_542);
if (lean_is_scalar(x_543)) {
 x_550 = lean_alloc_ctor(0, 5, 0);
} else {
 x_550 = x_543;
}
lean_ctor_set(x_550, 0, x_548);
lean_ctor_set(x_550, 1, x_549);
lean_ctor_set(x_550, 2, x_547);
lean_ctor_set(x_550, 3, x_546);
lean_ctor_set(x_550, 4, x_545);
x_551 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_551, 0, x_550);
lean_ctor_set(x_551, 1, x_544);
x_552 = l_ReaderT_instMonad___redArg(x_551);
x_553 = l_ReaderT_instMonad___redArg(x_552);
x_554 = l_ReaderT_instMonad___redArg(x_553);
x_555 = lean_ctor_get(x_554, 0);
lean_inc_ref(x_555);
if (lean_is_exclusive(x_554)) {
 lean_ctor_release(x_554, 0);
 lean_ctor_release(x_554, 1);
 x_556 = x_554;
} else {
 lean_dec_ref(x_554);
 x_556 = lean_box(0);
}
x_557 = lean_ctor_get(x_555, 0);
lean_inc_ref(x_557);
lean_dec_ref(x_555);
lean_inc_ref(x_557);
x_558 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_558, 0, x_557);
x_559 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_559, 0, x_557);
if (lean_is_scalar(x_556)) {
 x_560 = lean_alloc_ctor(0, 2, 0);
} else {
 x_560 = x_556;
}
lean_ctor_set(x_560, 0, x_558);
lean_ctor_set(x_560, 1, x_559);
x_561 = l_Lake_EquipT_instFunctor___redArg(x_560);
x_562 = l_Lake_instMonadWorkspaceJobM;
lean_inc_ref(x_5);
x_563 = l_Lake_Package_isArtifactCacheEnabled___redArg(x_561, x_562, x_5);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_564 = lean_apply_7(x_563, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_564) == 0)
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; uint8_t x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_613; 
x_565 = lean_ctor_get(x_564, 1);
lean_inc(x_565);
x_566 = lean_ctor_get(x_564, 0);
lean_inc(x_566);
lean_dec_ref(x_564);
x_567 = lean_ctor_get(x_565, 0);
lean_inc_ref(x_567);
x_568 = lean_ctor_get_uint8(x_565, sizeof(void*)*3);
x_569 = lean_ctor_get(x_565, 1);
lean_inc_ref(x_569);
x_570 = lean_ctor_get(x_565, 2);
lean_inc(x_570);
if (lean_is_exclusive(x_565)) {
 lean_ctor_release(x_565, 0);
 lean_ctor_release(x_565, 1);
 lean_ctor_release(x_565, 2);
 x_571 = x_565;
} else {
 lean_dec_ref(x_565);
 x_571 = lean_box(0);
}
x_572 = l_Lake_Package_cacheScope(x_5);
lean_inc_ref(x_4);
x_613 = l_Lake_Cache_readOutputs_x3f(x_4, x_572, x_2, x_567);
if (lean_obj_tag(x_613) == 0)
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; 
x_614 = lean_ctor_get(x_613, 0);
lean_inc(x_614);
x_615 = lean_ctor_get(x_613, 1);
lean_inc(x_615);
lean_dec_ref(x_613);
if (lean_is_scalar(x_571)) {
 x_616 = lean_alloc_ctor(0, 3, 1);
} else {
 x_616 = x_571;
}
lean_ctor_set(x_616, 0, x_615);
lean_ctor_set(x_616, 1, x_569);
lean_ctor_set(x_616, 2, x_570);
lean_ctor_set_uint8(x_616, sizeof(void*)*3, x_568);
if (lean_obj_tag(x_614) == 0)
{
x_573 = x_6;
x_574 = x_7;
x_575 = x_8;
x_576 = x_9;
x_577 = x_10;
x_578 = x_616;
x_579 = lean_box(0);
goto block_612;
}
else
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; 
x_617 = lean_ctor_get(x_614, 0);
lean_inc(x_617);
if (lean_is_exclusive(x_614)) {
 lean_ctor_release(x_614, 0);
 x_618 = x_614;
} else {
 lean_dec_ref(x_614);
 x_618 = lean_box(0);
}
lean_inc_ref(x_1);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_619 = lean_apply_8(x_1, x_617, x_6, x_7, x_8, x_9, x_10, x_616, lean_box(0));
if (lean_obj_tag(x_619) == 0)
{
lean_object* x_620; 
x_620 = lean_ctor_get(x_619, 0);
lean_inc(x_620);
if (lean_obj_tag(x_620) == 0)
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; uint8_t x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; uint8_t x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; 
lean_dec(x_618);
x_621 = lean_ctor_get(x_619, 1);
lean_inc(x_621);
lean_dec_ref(x_619);
x_622 = lean_ctor_get(x_620, 0);
lean_inc(x_622);
lean_dec_ref(x_620);
x_623 = lean_ctor_get(x_621, 0);
lean_inc_ref(x_623);
x_624 = lean_ctor_get_uint8(x_621, sizeof(void*)*3);
x_625 = lean_ctor_get(x_621, 1);
lean_inc_ref(x_625);
x_626 = lean_ctor_get(x_621, 2);
lean_inc(x_626);
if (lean_is_exclusive(x_621)) {
 lean_ctor_release(x_621, 0);
 lean_ctor_release(x_621, 1);
 lean_ctor_release(x_621, 2);
 x_627 = x_621;
} else {
 lean_dec_ref(x_621);
 x_627 = lean_box(0);
}
x_628 = l_Lake_getArtifacts_x3f___redArg___closed__0;
x_629 = l_Lake_Hash_hex(x_2);
x_630 = lean_unsigned_to_nat(7u);
x_631 = lean_unsigned_to_nat(0u);
x_632 = lean_string_utf8_byte_size(x_629);
lean_inc_ref(x_629);
x_633 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_633, 0, x_629);
lean_ctor_set(x_633, 1, x_631);
lean_ctor_set(x_633, 2, x_632);
x_634 = l_Substring_nextn(x_633, x_630, x_631);
lean_dec_ref(x_633);
x_635 = lean_string_utf8_extract(x_629, x_631, x_634);
lean_dec(x_634);
lean_dec_ref(x_629);
x_636 = lean_string_append(x_628, x_635);
lean_dec_ref(x_635);
x_637 = l_Lake_getArtifacts_x3f___redArg___closed__1;
x_638 = lean_string_append(x_636, x_637);
x_639 = lean_string_append(x_638, x_622);
lean_dec(x_622);
x_640 = 2;
x_641 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_641, 0, x_639);
lean_ctor_set_uint8(x_641, sizeof(void*)*1, x_640);
x_642 = lean_array_push(x_623, x_641);
if (lean_is_scalar(x_627)) {
 x_643 = lean_alloc_ctor(0, 3, 1);
} else {
 x_643 = x_627;
}
lean_ctor_set(x_643, 0, x_642);
lean_ctor_set(x_643, 1, x_625);
lean_ctor_set(x_643, 2, x_626);
lean_ctor_set_uint8(x_643, sizeof(void*)*3, x_624);
x_573 = x_6;
x_574 = x_7;
x_575 = x_8;
x_576 = x_9;
x_577 = x_10;
x_578 = x_643;
x_579 = lean_box(0);
goto block_612;
}
else
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; 
lean_dec_ref(x_572);
lean_dec(x_566);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_644 = lean_ctor_get(x_619, 1);
lean_inc(x_644);
if (lean_is_exclusive(x_619)) {
 lean_ctor_release(x_619, 0);
 lean_ctor_release(x_619, 1);
 x_645 = x_619;
} else {
 lean_dec_ref(x_619);
 x_645 = lean_box(0);
}
x_646 = lean_ctor_get(x_620, 0);
lean_inc(x_646);
lean_dec_ref(x_620);
if (lean_is_scalar(x_618)) {
 x_647 = lean_alloc_ctor(1, 1, 0);
} else {
 x_647 = x_618;
}
lean_ctor_set(x_647, 0, x_646);
if (lean_is_scalar(x_645)) {
 x_648 = lean_alloc_ctor(0, 2, 0);
} else {
 x_648 = x_645;
}
lean_ctor_set(x_648, 0, x_647);
lean_ctor_set(x_648, 1, x_644);
return x_648;
}
}
else
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; 
lean_dec(x_618);
lean_dec_ref(x_572);
lean_dec(x_566);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_649 = lean_ctor_get(x_619, 0);
lean_inc(x_649);
x_650 = lean_ctor_get(x_619, 1);
lean_inc(x_650);
if (lean_is_exclusive(x_619)) {
 lean_ctor_release(x_619, 0);
 lean_ctor_release(x_619, 1);
 x_651 = x_619;
} else {
 lean_dec_ref(x_619);
 x_651 = lean_box(0);
}
if (lean_is_scalar(x_651)) {
 x_652 = lean_alloc_ctor(1, 2, 0);
} else {
 x_652 = x_651;
}
lean_ctor_set(x_652, 0, x_649);
lean_ctor_set(x_652, 1, x_650);
return x_652;
}
}
}
else
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; 
lean_dec_ref(x_572);
lean_dec(x_566);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_653 = lean_ctor_get(x_613, 0);
lean_inc(x_653);
x_654 = lean_ctor_get(x_613, 1);
lean_inc(x_654);
if (lean_is_exclusive(x_613)) {
 lean_ctor_release(x_613, 0);
 lean_ctor_release(x_613, 1);
 x_655 = x_613;
} else {
 lean_dec_ref(x_613);
 x_655 = lean_box(0);
}
if (lean_is_scalar(x_571)) {
 x_656 = lean_alloc_ctor(0, 3, 1);
} else {
 x_656 = x_571;
}
lean_ctor_set(x_656, 0, x_654);
lean_ctor_set(x_656, 1, x_569);
lean_ctor_set(x_656, 2, x_570);
lean_ctor_set_uint8(x_656, sizeof(void*)*3, x_568);
if (lean_is_scalar(x_655)) {
 x_657 = lean_alloc_ctor(1, 2, 0);
} else {
 x_657 = x_655;
}
lean_ctor_set(x_657, 0, x_653);
lean_ctor_set(x_657, 1, x_656);
return x_657;
}
block_612:
{
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_580; uint64_t x_581; lean_object* x_582; uint8_t x_583; 
x_580 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_580);
lean_dec_ref(x_3);
x_581 = lean_ctor_get_uint64(x_580, sizeof(void*)*3);
x_582 = lean_ctor_get(x_580, 1);
lean_inc(x_582);
lean_dec_ref(x_580);
x_583 = lean_uint64_dec_eq(x_581, x_2);
if (x_583 == 0)
{
lean_dec(x_582);
lean_dec_ref(x_577);
lean_dec(x_576);
lean_dec(x_575);
lean_dec(x_574);
lean_dec_ref(x_573);
lean_dec_ref(x_572);
lean_dec(x_566);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_13 = x_578;
x_14 = lean_box(0);
goto block_17;
}
else
{
if (lean_obj_tag(x_582) == 0)
{
lean_dec_ref(x_577);
lean_dec(x_576);
lean_dec(x_575);
lean_dec(x_574);
lean_dec_ref(x_573);
lean_dec_ref(x_572);
lean_dec(x_566);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_13 = x_578;
x_14 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_584; lean_object* x_585; 
x_584 = lean_ctor_get(x_582, 0);
lean_inc(x_584);
lean_dec_ref(x_582);
lean_inc(x_584);
x_585 = lean_apply_8(x_1, x_584, x_573, x_574, x_575, x_576, x_577, x_578, lean_box(0));
if (lean_obj_tag(x_585) == 0)
{
lean_object* x_586; 
x_586 = lean_ctor_get(x_585, 0);
lean_inc(x_586);
if (lean_obj_tag(x_586) == 0)
{
lean_object* x_587; 
lean_dec_ref(x_586);
lean_dec(x_584);
lean_dec_ref(x_572);
lean_dec(x_566);
lean_dec_ref(x_4);
x_587 = lean_ctor_get(x_585, 1);
lean_inc(x_587);
lean_dec_ref(x_585);
x_13 = x_587;
x_14 = lean_box(0);
goto block_17;
}
else
{
uint8_t x_588; 
x_588 = lean_unbox(x_566);
lean_dec(x_566);
if (x_588 == 0)
{
lean_object* x_589; lean_object* x_590; 
lean_dec(x_584);
lean_dec_ref(x_572);
lean_dec_ref(x_4);
x_589 = lean_ctor_get(x_585, 1);
lean_inc(x_589);
lean_dec_ref(x_585);
x_590 = lean_ctor_get(x_586, 0);
lean_inc(x_590);
lean_dec_ref(x_586);
x_18 = x_590;
x_19 = x_589;
x_20 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; uint8_t x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; 
x_591 = lean_ctor_get(x_585, 1);
lean_inc(x_591);
if (lean_is_exclusive(x_585)) {
 lean_ctor_release(x_585, 0);
 lean_ctor_release(x_585, 1);
 x_592 = x_585;
} else {
 lean_dec_ref(x_585);
 x_592 = lean_box(0);
}
x_593 = lean_ctor_get(x_586, 0);
lean_inc(x_593);
lean_dec_ref(x_586);
x_594 = lean_ctor_get(x_591, 0);
x_595 = lean_ctor_get_uint8(x_591, sizeof(void*)*3);
x_596 = lean_ctor_get(x_591, 1);
x_597 = lean_ctor_get(x_591, 2);
x_598 = l_Lake_Cache_writeOutputsCore(x_4, x_572, x_2, x_584);
lean_dec_ref(x_572);
if (lean_obj_tag(x_598) == 0)
{
lean_dec_ref(x_598);
lean_dec(x_592);
x_18 = x_593;
x_19 = x_591;
x_20 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; uint8_t x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; 
lean_inc(x_597);
lean_inc_ref(x_596);
lean_inc_ref(x_594);
lean_dec(x_593);
if (lean_is_exclusive(x_591)) {
 lean_ctor_release(x_591, 0);
 lean_ctor_release(x_591, 1);
 lean_ctor_release(x_591, 2);
 x_599 = x_591;
} else {
 lean_dec_ref(x_591);
 x_599 = lean_box(0);
}
x_600 = lean_ctor_get(x_598, 0);
lean_inc(x_600);
lean_dec_ref(x_598);
x_601 = lean_io_error_to_string(x_600);
x_602 = 3;
x_603 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_603, 0, x_601);
lean_ctor_set_uint8(x_603, sizeof(void*)*1, x_602);
x_604 = lean_array_get_size(x_594);
x_605 = lean_array_push(x_594, x_603);
if (lean_is_scalar(x_599)) {
 x_606 = lean_alloc_ctor(0, 3, 1);
} else {
 x_606 = x_599;
}
lean_ctor_set(x_606, 0, x_605);
lean_ctor_set(x_606, 1, x_596);
lean_ctor_set(x_606, 2, x_597);
lean_ctor_set_uint8(x_606, sizeof(void*)*3, x_595);
if (lean_is_scalar(x_592)) {
 x_607 = lean_alloc_ctor(1, 2, 0);
} else {
 x_607 = x_592;
 lean_ctor_set_tag(x_607, 1);
}
lean_ctor_set(x_607, 0, x_604);
lean_ctor_set(x_607, 1, x_606);
return x_607;
}
}
}
}
else
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; 
lean_dec(x_584);
lean_dec_ref(x_572);
lean_dec(x_566);
lean_dec_ref(x_4);
x_608 = lean_ctor_get(x_585, 0);
lean_inc(x_608);
x_609 = lean_ctor_get(x_585, 1);
lean_inc(x_609);
if (lean_is_exclusive(x_585)) {
 lean_ctor_release(x_585, 0);
 lean_ctor_release(x_585, 1);
 x_610 = x_585;
} else {
 lean_dec_ref(x_585);
 x_610 = lean_box(0);
}
if (lean_is_scalar(x_610)) {
 x_611 = lean_alloc_ctor(1, 2, 0);
} else {
 x_611 = x_610;
}
lean_ctor_set(x_611, 0, x_608);
lean_ctor_set(x_611, 1, x_609);
return x_611;
}
}
}
}
else
{
lean_dec_ref(x_577);
lean_dec(x_576);
lean_dec(x_575);
lean_dec(x_574);
lean_dec_ref(x_573);
lean_dec_ref(x_572);
lean_dec(x_566);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_13 = x_578;
x_14 = lean_box(0);
goto block_17;
}
}
}
else
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_658 = lean_ctor_get(x_564, 0);
lean_inc(x_658);
x_659 = lean_ctor_get(x_564, 1);
lean_inc(x_659);
if (lean_is_exclusive(x_564)) {
 lean_ctor_release(x_564, 0);
 lean_ctor_release(x_564, 1);
 x_660 = x_564;
} else {
 lean_dec_ref(x_564);
 x_660 = lean_box(0);
}
if (lean_is_scalar(x_660)) {
 x_661 = lean_alloc_ctor(1, 2, 0);
} else {
 x_661 = x_660;
}
lean_ctor_set(x_661, 0, x_658);
lean_ctor_set(x_661, 1, x_659);
return x_661;
}
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
block_23:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lake_getArtifacts_x3f___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint64_t x_13; lean_object* x_14; 
x_13 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_14 = l_Lake_getArtifacts_x3f___redArg(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint64_t x_14; lean_object* x_15; 
x_14 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_15 = l_Lake_getArtifacts_x3f(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lake_Cache_getArtifact___boxed), 3, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_1);
x_5 = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, lean_box(0));
lean_closure_set(x_5, 2, x_4);
x_6 = lean_apply_2(x_2, lean_box(0), x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ill-formed artifact output `", 28, 28);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`: ", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_cacheArtifact___redArg___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec_ref(x_5);
lean_inc(x_4);
x_9 = l_Lake_ArtifactDescr_fromJson_x3f(x_4);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__0;
x_13 = lean_unsigned_to_nat(80u);
x_14 = l_Lean_Json_pretty(x_4, x_13);
x_15 = lean_string_append(x_12, x_14);
lean_dec_ref(x_14);
x_16 = l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_string_append(x_17, x_11);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_18);
x_19 = lean_apply_2(x_8, lean_box(0), x_9);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_9, 0);
lean_inc(x_20);
lean_dec(x_9);
x_21 = l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__0;
x_22 = lean_unsigned_to_nat(80u);
x_23 = l_Lean_Json_pretty(x_4, x_22);
x_24 = lean_string_append(x_21, x_23);
lean_dec_ref(x_23);
x_25 = l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__1;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_string_append(x_26, x_20);
lean_dec(x_20);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_apply_2(x_8, lean_box(0), x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_8);
lean_dec(x_4);
x_30 = lean_ctor_get(x_9, 0);
lean_inc(x_30);
lean_dec_ref(x_9);
x_31 = lean_ctor_get(x_7, 0);
lean_inc(x_31);
lean_dec_ref(x_7);
x_32 = l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__2;
x_33 = lean_alloc_closure((void*)(l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___lam__1), 3, 2);
lean_closure_set(x_33, 0, x_30);
lean_closure_set(x_33, 1, x_2);
x_34 = lean_apply_4(x_31, lean_box(0), lean_box(0), x_32, x_1);
x_35 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_34, x_33);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec_ref(x_6);
lean_inc(x_5);
x_10 = l_Lake_ArtifactDescr_fromJson_x3f(x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__0;
x_14 = lean_unsigned_to_nat(80u);
x_15 = l_Lean_Json_pretty(x_5, x_14);
x_16 = lean_string_append(x_13, x_15);
lean_dec_ref(x_15);
x_17 = l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_12);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_19);
x_20 = lean_apply_2(x_9, lean_box(0), x_10);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_10, 0);
lean_inc(x_21);
lean_dec(x_10);
x_22 = l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__0;
x_23 = lean_unsigned_to_nat(80u);
x_24 = l_Lean_Json_pretty(x_5, x_23);
x_25 = lean_string_append(x_22, x_24);
lean_dec_ref(x_24);
x_26 = l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__1;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_string_append(x_27, x_21);
lean_dec(x_21);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_apply_2(x_9, lean_box(0), x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_9);
lean_dec(x_5);
x_31 = lean_ctor_get(x_10, 0);
lean_inc(x_31);
lean_dec_ref(x_10);
x_32 = lean_ctor_get(x_8, 0);
lean_inc(x_32);
lean_dec_ref(x_8);
x_33 = l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__2;
x_34 = lean_alloc_closure((void*)(l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___lam__1), 3, 2);
lean_closure_set(x_34, 0, x_31);
lean_closure_set(x_34, 1, x_3);
x_35 = lean_apply_4(x_32, lean_box(0), lean_box(0), x_33, x_2);
x_36 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_35, x_34);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsArtifactOfMonadWorkspaceOfMonadLiftTBaseIOOfMonad___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f), 5, 4);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, x_1);
lean_closure_set(x_4, 2, x_2);
lean_closure_set(x_4, 3, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsArtifactOfMonadWorkspaceOfMonadLiftTBaseIOOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f), 5, 4);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_3);
lean_closure_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
lean_inc_ref(x_1);
x_7 = l_Lake_fetchFileHash___redArg(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_19; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
x_19 = lean_io_metadata(x_1);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_21);
lean_dec(x_20);
x_11 = x_9;
x_12 = lean_box(0);
x_13 = x_21;
goto block_18;
}
else
{
lean_object* x_22; 
lean_dec_ref(x_19);
x_22 = l_Lake_platformTrace___closed__6;
x_11 = x_9;
x_12 = lean_box(0);
x_13 = x_22;
goto block_18;
}
block_18:
{
lean_object* x_14; uint64_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_14, 0, x_2);
x_15 = lean_unbox_uint64(x_8);
lean_dec(x_8);
lean_ctor_set_uint64(x_14, sizeof(void*)*1, x_15);
lean_inc_ref(x_1);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_1);
lean_ctor_set(x_16, 2, x_1);
lean_ctor_set(x_16, 3, x_13);
if (lean_is_scalar(x_10)) {
 x_17 = lean_alloc_ctor(0, 2, 0);
} else {
 x_17 = x_10;
}
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
}
else
{
uint8_t x_23; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
return x_7;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_7);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_computeArtifact___redArg(x_1, x_2, x_3, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
x_8 = l_Lake_computeArtifact___redArg(x_1, x_2, x_7, x_4, x_5);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifact___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
x_12 = l_Lake_computeArtifact(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at_____private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_io_mono_ms_now();
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_nat_sub(x_5, x_1);
lean_dec(x_5);
x_9 = lean_box(0);
x_10 = lean_nat_add(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
lean_ctor_set(x_3, 2, x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_12);
lean_dec(x_3);
x_16 = lean_nat_sub(x_5, x_1);
lean_dec(x_5);
x_17 = lean_box(0);
x_18 = lean_nat_add(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*3, x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at_____private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get_uint8(x_20, sizeof(void*)*2 + 2);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get_uint8(x_13, sizeof(void*)*3);
x_25 = lean_io_mono_ms_now();
x_26 = l_Lake_JobAction_merge(x_24, x_8);
lean_inc_ref(x_23);
lean_ctor_set_uint8(x_13, sizeof(void*)*3, x_26);
lean_inc_ref(x_12);
x_27 = lean_apply_7(x_1, x_5, x_9, x_10, x_11, x_12, x_13, lean_box(0));
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_dec_ref(x_27);
x_36 = lean_ctor_get(x_35, 0);
x_37 = lean_ctor_get_uint8(x_35, sizeof(void*)*3);
x_38 = lean_ctor_get(x_35, 1);
x_39 = lean_ctor_get(x_35, 2);
lean_inc_ref(x_2);
x_40 = l_Lake_clearFileHash(x_2);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
lean_dec_ref(x_40);
x_41 = l_Lake_removeFileIfExists(x_3);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_42 = x_41;
} else {
 lean_dec_ref(x_41);
 x_42 = lean_box(0);
}
x_43 = l_Lake_computeArtifact___redArg(x_2, x_4, x_21, x_12, x_35);
lean_dec_ref(x_12);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; uint64_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_46 = x_43;
} else {
 lean_dec_ref(x_43);
 x_46 = lean_box(0);
}
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_44, 0);
x_49 = lean_ctor_get_uint8(x_44, sizeof(void*)*3);
x_50 = lean_ctor_get(x_44, 1);
x_51 = lean_ctor_get(x_44, 2);
x_52 = lean_ctor_get_uint64(x_47, sizeof(void*)*1);
x_53 = lean_ctor_get(x_47, 0);
x_54 = lean_array_get_size(x_23);
lean_dec_ref(x_23);
x_55 = lean_array_get_size(x_48);
lean_inc(x_55);
x_56 = l_Array_extract___redArg(x_48, x_54, x_55);
x_93 = lean_string_utf8_byte_size(x_53);
x_94 = lean_unsigned_to_nat(0u);
x_95 = lean_nat_dec_eq(x_93, x_94);
lean_dec(x_93);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = l_Lake_Hash_hex(x_52);
x_97 = l_Lake_instToOutputJsonArtifact___lam__0___closed__0;
x_98 = lean_string_append(x_96, x_97);
x_99 = lean_string_append(x_98, x_53);
x_57 = x_99;
goto block_92;
}
else
{
lean_object* x_100; 
x_100 = l_Lake_Hash_hex(x_52);
x_57 = x_100;
goto block_92;
}
block_92:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
if (lean_is_scalar(x_42)) {
 x_58 = lean_alloc_ctor(3, 1, 0);
} else {
 x_58 = x_42;
 lean_ctor_set_tag(x_58, 3);
}
lean_ctor_set(x_58, 0, x_57);
x_59 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_6, x_58, x_56);
x_60 = l_Lake_BuildMetadata_writeFile(x_7, x_59);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
lean_dec(x_55);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_62 = lean_ctor_get(x_60, 0);
lean_dec(x_62);
x_63 = lean_box(0);
lean_inc(x_45);
if (lean_is_scalar(x_46)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_46;
 lean_ctor_set_tag(x_64, 1);
}
lean_ctor_set(x_64, 0, x_45);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set_tag(x_60, 1);
lean_ctor_set(x_60, 0, x_64);
x_65 = l_Lake_buildAction___at_____private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(x_25, x_60, x_44);
lean_dec_ref(x_60);
lean_dec(x_25);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_65, 0);
lean_dec(x_67);
lean_ctor_set(x_65, 0, x_45);
return x_65;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_45);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_60);
x_70 = lean_box(0);
lean_inc(x_45);
if (lean_is_scalar(x_46)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_46;
 lean_ctor_set_tag(x_71, 1);
}
lean_ctor_set(x_71, 0, x_45);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = l_Lake_buildAction___at_____private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(x_25, x_72, x_44);
lean_dec_ref(x_72);
lean_dec(x_25);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_75 = x_73;
} else {
 lean_dec_ref(x_73);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_45);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_inc(x_51);
lean_inc_ref(x_50);
lean_inc_ref(x_48);
lean_dec(x_46);
lean_dec(x_45);
x_77 = !lean_is_exclusive(x_44);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; 
x_78 = lean_ctor_get(x_44, 2);
lean_dec(x_78);
x_79 = lean_ctor_get(x_44, 1);
lean_dec(x_79);
x_80 = lean_ctor_get(x_44, 0);
lean_dec(x_80);
x_81 = lean_ctor_get(x_60, 0);
lean_inc(x_81);
lean_dec_ref(x_60);
x_82 = lean_io_error_to_string(x_81);
x_83 = 3;
x_84 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set_uint8(x_84, sizeof(void*)*1, x_83);
x_85 = lean_array_push(x_48, x_84);
lean_ctor_set(x_44, 0, x_85);
x_28 = x_55;
x_29 = x_44;
x_30 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_44);
x_86 = lean_ctor_get(x_60, 0);
lean_inc(x_86);
lean_dec_ref(x_60);
x_87 = lean_io_error_to_string(x_86);
x_88 = 3;
x_89 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set_uint8(x_89, sizeof(void*)*1, x_88);
x_90 = lean_array_push(x_48, x_89);
x_91 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_50);
lean_ctor_set(x_91, 2, x_51);
lean_ctor_set_uint8(x_91, sizeof(void*)*3, x_49);
x_28 = x_55;
x_29 = x_91;
x_30 = lean_box(0);
goto block_34;
}
}
}
}
else
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_42);
lean_dec_ref(x_23);
x_101 = lean_ctor_get(x_43, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_43, 1);
lean_inc(x_102);
lean_dec_ref(x_43);
x_28 = x_101;
x_29 = x_102;
x_30 = lean_box(0);
goto block_34;
}
}
else
{
uint8_t x_103; 
lean_inc(x_39);
lean_inc_ref(x_38);
lean_inc_ref(x_36);
lean_dec_ref(x_23);
lean_dec_ref(x_12);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_103 = !lean_is_exclusive(x_35);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_104 = lean_ctor_get(x_35, 2);
lean_dec(x_104);
x_105 = lean_ctor_get(x_35, 1);
lean_dec(x_105);
x_106 = lean_ctor_get(x_35, 0);
lean_dec(x_106);
x_107 = lean_ctor_get(x_41, 0);
lean_inc(x_107);
lean_dec_ref(x_41);
x_108 = lean_io_error_to_string(x_107);
x_109 = 3;
x_110 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set_uint8(x_110, sizeof(void*)*1, x_109);
x_111 = lean_array_get_size(x_36);
x_112 = lean_array_push(x_36, x_110);
lean_ctor_set(x_35, 0, x_112);
x_28 = x_111;
x_29 = x_35;
x_30 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_35);
x_113 = lean_ctor_get(x_41, 0);
lean_inc(x_113);
lean_dec_ref(x_41);
x_114 = lean_io_error_to_string(x_113);
x_115 = 3;
x_116 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set_uint8(x_116, sizeof(void*)*1, x_115);
x_117 = lean_array_get_size(x_36);
x_118 = lean_array_push(x_36, x_116);
x_119 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_38);
lean_ctor_set(x_119, 2, x_39);
lean_ctor_set_uint8(x_119, sizeof(void*)*3, x_37);
x_28 = x_117;
x_29 = x_119;
x_30 = lean_box(0);
goto block_34;
}
}
}
else
{
uint8_t x_120; 
lean_inc(x_39);
lean_inc_ref(x_38);
lean_inc_ref(x_36);
lean_dec_ref(x_23);
lean_dec_ref(x_12);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_120 = !lean_is_exclusive(x_35);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_121 = lean_ctor_get(x_35, 2);
lean_dec(x_121);
x_122 = lean_ctor_get(x_35, 1);
lean_dec(x_122);
x_123 = lean_ctor_get(x_35, 0);
lean_dec(x_123);
x_124 = lean_ctor_get(x_40, 0);
lean_inc(x_124);
lean_dec_ref(x_40);
x_125 = lean_io_error_to_string(x_124);
x_126 = 3;
x_127 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set_uint8(x_127, sizeof(void*)*1, x_126);
x_128 = lean_array_get_size(x_36);
x_129 = lean_array_push(x_36, x_127);
lean_ctor_set(x_35, 0, x_129);
x_28 = x_128;
x_29 = x_35;
x_30 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_35);
x_130 = lean_ctor_get(x_40, 0);
lean_inc(x_130);
lean_dec_ref(x_40);
x_131 = lean_io_error_to_string(x_130);
x_132 = 3;
x_133 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set_uint8(x_133, sizeof(void*)*1, x_132);
x_134 = lean_array_get_size(x_36);
x_135 = lean_array_push(x_36, x_133);
x_136 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_38);
lean_ctor_set(x_136, 2, x_39);
lean_ctor_set_uint8(x_136, sizeof(void*)*3, x_37);
x_28 = x_134;
x_29 = x_136;
x_30 = lean_box(0);
goto block_34;
}
}
}
else
{
lean_object* x_137; lean_object* x_138; 
lean_dec_ref(x_23);
lean_dec_ref(x_12);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_137 = lean_ctor_get(x_27, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_27, 1);
lean_inc(x_138);
lean_dec_ref(x_27);
x_28 = x_137;
x_29 = x_138;
x_30 = lean_box(0);
goto block_34;
}
block_34:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_box(0);
x_32 = l_Lake_buildAction___at_____private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(x_25, x_31, x_29);
lean_dec(x_25);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec_ref(x_32);
x_15 = x_28;
x_16 = x_33;
x_17 = lean_box(0);
goto block_19;
}
}
else
{
lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_139 = lean_ctor_get(x_13, 0);
x_140 = lean_ctor_get_uint8(x_13, sizeof(void*)*3);
x_141 = lean_ctor_get(x_13, 1);
x_142 = lean_ctor_get(x_13, 2);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_139);
lean_dec(x_13);
x_143 = lean_io_mono_ms_now();
x_144 = l_Lake_JobAction_merge(x_140, x_8);
lean_inc_ref(x_139);
x_145 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_145, 0, x_139);
lean_ctor_set(x_145, 1, x_141);
lean_ctor_set(x_145, 2, x_142);
lean_ctor_set_uint8(x_145, sizeof(void*)*3, x_144);
lean_inc_ref(x_12);
x_146 = lean_apply_7(x_1, x_5, x_9, x_10, x_11, x_12, x_145, lean_box(0));
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_154 = lean_ctor_get(x_146, 1);
lean_inc(x_154);
lean_dec_ref(x_146);
x_155 = lean_ctor_get(x_154, 0);
x_156 = lean_ctor_get_uint8(x_154, sizeof(void*)*3);
x_157 = lean_ctor_get(x_154, 1);
x_158 = lean_ctor_get(x_154, 2);
lean_inc_ref(x_2);
x_159 = l_Lake_clearFileHash(x_2);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; 
lean_dec_ref(x_159);
x_160 = l_Lake_removeFileIfExists(x_3);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; 
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 x_161 = x_160;
} else {
 lean_dec_ref(x_160);
 x_161 = lean_box(0);
}
x_162 = l_Lake_computeArtifact___redArg(x_2, x_4, x_21, x_12, x_154);
lean_dec_ref(x_12);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; lean_object* x_169; lean_object* x_170; uint64_t x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 0);
lean_inc(x_164);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_165 = x_162;
} else {
 lean_dec_ref(x_162);
 x_165 = lean_box(0);
}
x_166 = lean_ctor_get(x_164, 0);
x_167 = lean_ctor_get(x_163, 0);
x_168 = lean_ctor_get_uint8(x_163, sizeof(void*)*3);
x_169 = lean_ctor_get(x_163, 1);
x_170 = lean_ctor_get(x_163, 2);
x_171 = lean_ctor_get_uint64(x_166, sizeof(void*)*1);
x_172 = lean_ctor_get(x_166, 0);
x_173 = lean_array_get_size(x_139);
lean_dec_ref(x_139);
x_174 = lean_array_get_size(x_167);
lean_inc(x_174);
x_175 = l_Array_extract___redArg(x_167, x_173, x_174);
x_196 = lean_string_utf8_byte_size(x_172);
x_197 = lean_unsigned_to_nat(0u);
x_198 = lean_nat_dec_eq(x_196, x_197);
lean_dec(x_196);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_199 = l_Lake_Hash_hex(x_171);
x_200 = l_Lake_instToOutputJsonArtifact___lam__0___closed__0;
x_201 = lean_string_append(x_199, x_200);
x_202 = lean_string_append(x_201, x_172);
x_176 = x_202;
goto block_195;
}
else
{
lean_object* x_203; 
x_203 = l_Lake_Hash_hex(x_171);
x_176 = x_203;
goto block_195;
}
block_195:
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
if (lean_is_scalar(x_161)) {
 x_177 = lean_alloc_ctor(3, 1, 0);
} else {
 x_177 = x_161;
 lean_ctor_set_tag(x_177, 3);
}
lean_ctor_set(x_177, 0, x_176);
x_178 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_6, x_177, x_175);
x_179 = l_Lake_BuildMetadata_writeFile(x_7, x_178);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_174);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 x_180 = x_179;
} else {
 lean_dec_ref(x_179);
 x_180 = lean_box(0);
}
x_181 = lean_box(0);
lean_inc(x_164);
if (lean_is_scalar(x_165)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_165;
 lean_ctor_set_tag(x_182, 1);
}
lean_ctor_set(x_182, 0, x_164);
lean_ctor_set(x_182, 1, x_181);
if (lean_is_scalar(x_180)) {
 x_183 = lean_alloc_ctor(1, 1, 0);
} else {
 x_183 = x_180;
 lean_ctor_set_tag(x_183, 1);
}
lean_ctor_set(x_183, 0, x_182);
x_184 = l_Lake_buildAction___at_____private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(x_143, x_183, x_163);
lean_dec_ref(x_183);
lean_dec(x_143);
x_185 = lean_ctor_get(x_184, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_186 = x_184;
} else {
 lean_dec_ref(x_184);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_164);
lean_ctor_set(x_187, 1, x_185);
return x_187;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_inc(x_170);
lean_inc_ref(x_169);
lean_inc_ref(x_167);
lean_dec(x_165);
lean_dec(x_164);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 lean_ctor_release(x_163, 2);
 x_188 = x_163;
} else {
 lean_dec_ref(x_163);
 x_188 = lean_box(0);
}
x_189 = lean_ctor_get(x_179, 0);
lean_inc(x_189);
lean_dec_ref(x_179);
x_190 = lean_io_error_to_string(x_189);
x_191 = 3;
x_192 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set_uint8(x_192, sizeof(void*)*1, x_191);
x_193 = lean_array_push(x_167, x_192);
if (lean_is_scalar(x_188)) {
 x_194 = lean_alloc_ctor(0, 3, 1);
} else {
 x_194 = x_188;
}
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_169);
lean_ctor_set(x_194, 2, x_170);
lean_ctor_set_uint8(x_194, sizeof(void*)*3, x_168);
x_147 = x_174;
x_148 = x_194;
x_149 = lean_box(0);
goto block_153;
}
}
}
else
{
lean_object* x_204; lean_object* x_205; 
lean_dec(x_161);
lean_dec_ref(x_139);
x_204 = lean_ctor_get(x_162, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_162, 1);
lean_inc(x_205);
lean_dec_ref(x_162);
x_147 = x_204;
x_148 = x_205;
x_149 = lean_box(0);
goto block_153;
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc_ref(x_155);
lean_dec_ref(x_139);
lean_dec_ref(x_12);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 lean_ctor_release(x_154, 2);
 x_206 = x_154;
} else {
 lean_dec_ref(x_154);
 x_206 = lean_box(0);
}
x_207 = lean_ctor_get(x_160, 0);
lean_inc(x_207);
lean_dec_ref(x_160);
x_208 = lean_io_error_to_string(x_207);
x_209 = 3;
x_210 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set_uint8(x_210, sizeof(void*)*1, x_209);
x_211 = lean_array_get_size(x_155);
x_212 = lean_array_push(x_155, x_210);
if (lean_is_scalar(x_206)) {
 x_213 = lean_alloc_ctor(0, 3, 1);
} else {
 x_213 = x_206;
}
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_157);
lean_ctor_set(x_213, 2, x_158);
lean_ctor_set_uint8(x_213, sizeof(void*)*3, x_156);
x_147 = x_211;
x_148 = x_213;
x_149 = lean_box(0);
goto block_153;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_inc(x_158);
lean_inc_ref(x_157);
lean_inc_ref(x_155);
lean_dec_ref(x_139);
lean_dec_ref(x_12);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 lean_ctor_release(x_154, 2);
 x_214 = x_154;
} else {
 lean_dec_ref(x_154);
 x_214 = lean_box(0);
}
x_215 = lean_ctor_get(x_159, 0);
lean_inc(x_215);
lean_dec_ref(x_159);
x_216 = lean_io_error_to_string(x_215);
x_217 = 3;
x_218 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set_uint8(x_218, sizeof(void*)*1, x_217);
x_219 = lean_array_get_size(x_155);
x_220 = lean_array_push(x_155, x_218);
if (lean_is_scalar(x_214)) {
 x_221 = lean_alloc_ctor(0, 3, 1);
} else {
 x_221 = x_214;
}
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_157);
lean_ctor_set(x_221, 2, x_158);
lean_ctor_set_uint8(x_221, sizeof(void*)*3, x_156);
x_147 = x_219;
x_148 = x_221;
x_149 = lean_box(0);
goto block_153;
}
}
else
{
lean_object* x_222; lean_object* x_223; 
lean_dec_ref(x_139);
lean_dec_ref(x_12);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_222 = lean_ctor_get(x_146, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_146, 1);
lean_inc(x_223);
lean_dec_ref(x_146);
x_147 = x_222;
x_148 = x_223;
x_149 = lean_box(0);
goto block_153;
}
block_153:
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_box(0);
x_151 = l_Lake_buildAction___at_____private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(x_143, x_150, x_148);
lean_dec(x_143);
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
lean_dec_ref(x_151);
x_15 = x_147;
x_16 = x_152;
x_17 = lean_box(0);
goto block_19;
}
}
}
else
{
uint8_t x_224; 
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_224 = !lean_is_exclusive(x_13);
if (x_224 == 0)
{
lean_object* x_225; uint8_t x_226; uint8_t x_227; uint8_t x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_225 = lean_ctor_get(x_13, 0);
x_226 = lean_ctor_get_uint8(x_13, sizeof(void*)*3);
x_227 = 3;
x_228 = l_Lake_JobAction_merge(x_226, x_227);
x_229 = l_Lake_buildAction___redArg___closed__1;
x_230 = lean_array_get_size(x_225);
x_231 = lean_array_push(x_225, x_229);
lean_ctor_set(x_13, 0, x_231);
lean_ctor_set_uint8(x_13, sizeof(void*)*3, x_228);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_13);
return x_232;
}
else
{
lean_object* x_233; uint8_t x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; uint8_t x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_233 = lean_ctor_get(x_13, 0);
x_234 = lean_ctor_get_uint8(x_13, sizeof(void*)*3);
x_235 = lean_ctor_get(x_13, 1);
x_236 = lean_ctor_get(x_13, 2);
lean_inc(x_236);
lean_inc(x_235);
lean_inc(x_233);
lean_dec(x_13);
x_237 = 3;
x_238 = l_Lake_JobAction_merge(x_234, x_237);
x_239 = l_Lake_buildAction___redArg___closed__1;
x_240 = lean_array_get_size(x_233);
x_241 = lean_array_push(x_233, x_239);
x_242 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_235);
lean_ctor_set(x_242, 2, x_236);
lean_ctor_set_uint8(x_242, sizeof(void*)*3, x_238);
x_243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_243, 0, x_240);
lean_ctor_set(x_243, 1, x_242);
return x_243;
}
}
block_19:
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = 3;
x_14 = l_Lake_buildAction___at_____private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(x_2, x_1, x_5, x_3, x_6, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at_____private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_buildAction___at_____private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at_____private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_8);
x_16 = l_Lake_buildAction___at_____private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_15, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheEnabled___at___Lake_buildArtifactUnlessUpToDate_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 4);
x_6 = lean_ctor_get(x_5, 25);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_7, 1);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*16 + 1);
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheEnabled___at___Lake_buildArtifactUnlessUpToDate_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Package_isArtifactCacheEnabled___at___Lake_buildArtifactUnlessUpToDate_spec__0___redArg(x_1, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___at___Lake_buildArtifactUnlessUpToDate_spec__1(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_97; 
x_23 = l_Lake_Package_isArtifactCacheEnabled___at___Lake_buildArtifactUnlessUpToDate_spec__0___redArg(x_5, x_9, x_10);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_26 = x_23;
} else {
 lean_dec_ref(x_23);
 x_26 = lean_box(0);
}
x_27 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_27);
x_28 = lean_ctor_get_uint8(x_24, sizeof(void*)*3);
x_29 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_24, 2);
lean_inc(x_30);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 x_31 = x_24;
} else {
 lean_dec_ref(x_24);
 x_31 = lean_box(0);
}
x_32 = l_Lake_Package_cacheScope(x_5);
lean_inc_ref(x_4);
x_97 = l_Lake_Cache_readOutputs_x3f(x_4, x_32, x_2, x_27);
if (lean_obj_tag(x_97) == 0)
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_97, 0);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_30);
lean_inc_ref(x_29);
lean_inc(x_100);
x_101 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_29);
lean_ctor_set(x_101, 2, x_30);
lean_ctor_set_uint8(x_101, sizeof(void*)*3, x_28);
if (lean_obj_tag(x_99) == 0)
{
lean_free_object(x_97);
lean_dec(x_100);
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
x_33 = x_9;
x_34 = x_101;
x_35 = lean_box(0);
goto block_73;
}
else
{
uint8_t x_102; 
x_102 = !lean_is_exclusive(x_99);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_99, 0);
lean_inc(x_103);
x_104 = l_Lake_ArtifactDescr_fromJson_x3f(x_103);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_free_object(x_99);
lean_dec_ref(x_101);
lean_free_object(x_97);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
lean_dec_ref(x_104);
x_106 = l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__0;
x_107 = lean_unsigned_to_nat(80u);
x_108 = l_Lean_Json_pretty(x_103, x_107);
x_109 = lean_string_append(x_106, x_108);
lean_dec_ref(x_108);
x_110 = l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__1;
x_111 = lean_string_append(x_109, x_110);
x_112 = lean_string_append(x_111, x_105);
lean_dec(x_105);
x_74 = x_112;
x_75 = x_100;
x_76 = x_28;
x_77 = x_29;
x_78 = x_30;
x_79 = lean_box(0);
goto block_96;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_103);
x_113 = lean_ctor_get(x_9, 1);
x_114 = lean_ctor_get(x_104, 0);
lean_inc(x_114);
lean_dec_ref(x_104);
x_115 = lean_ctor_get(x_113, 2);
lean_inc_ref(x_115);
x_116 = l_Lake_Cache_getArtifact(x_115, x_114);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; 
lean_dec(x_100);
lean_dec_ref(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_9);
lean_dec_ref(x_4);
lean_dec(x_3);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
lean_dec_ref(x_116);
lean_ctor_set(x_99, 0, x_117);
lean_ctor_set(x_97, 1, x_101);
return x_97;
}
else
{
lean_object* x_118; 
lean_free_object(x_99);
lean_dec_ref(x_101);
lean_free_object(x_97);
x_118 = lean_ctor_get(x_116, 0);
lean_inc(x_118);
lean_dec_ref(x_116);
x_74 = x_118;
x_75 = x_100;
x_76 = x_28;
x_77 = x_29;
x_78 = x_30;
x_79 = lean_box(0);
goto block_96;
}
}
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_99, 0);
lean_inc(x_119);
lean_dec(x_99);
lean_inc(x_119);
x_120 = l_Lake_ArtifactDescr_fromJson_x3f(x_119);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec_ref(x_101);
lean_free_object(x_97);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
lean_dec_ref(x_120);
x_122 = l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__0;
x_123 = lean_unsigned_to_nat(80u);
x_124 = l_Lean_Json_pretty(x_119, x_123);
x_125 = lean_string_append(x_122, x_124);
lean_dec_ref(x_124);
x_126 = l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__1;
x_127 = lean_string_append(x_125, x_126);
x_128 = lean_string_append(x_127, x_121);
lean_dec(x_121);
x_74 = x_128;
x_75 = x_100;
x_76 = x_28;
x_77 = x_29;
x_78 = x_30;
x_79 = lean_box(0);
goto block_96;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_119);
x_129 = lean_ctor_get(x_9, 1);
x_130 = lean_ctor_get(x_120, 0);
lean_inc(x_130);
lean_dec_ref(x_120);
x_131 = lean_ctor_get(x_129, 2);
lean_inc_ref(x_131);
x_132 = l_Lake_Cache_getArtifact(x_131, x_130);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_100);
lean_dec_ref(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_9);
lean_dec_ref(x_4);
lean_dec(x_3);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
lean_dec_ref(x_132);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_97, 1, x_101);
lean_ctor_set(x_97, 0, x_134);
return x_97;
}
else
{
lean_object* x_135; 
lean_dec_ref(x_101);
lean_free_object(x_97);
x_135 = lean_ctor_get(x_132, 0);
lean_inc(x_135);
lean_dec_ref(x_132);
x_74 = x_135;
x_75 = x_100;
x_76 = x_28;
x_77 = x_29;
x_78 = x_30;
x_79 = lean_box(0);
goto block_96;
}
}
}
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_97, 0);
x_137 = lean_ctor_get(x_97, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_97);
lean_inc(x_30);
lean_inc_ref(x_29);
lean_inc(x_137);
x_138 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_29);
lean_ctor_set(x_138, 2, x_30);
lean_ctor_set_uint8(x_138, sizeof(void*)*3, x_28);
if (lean_obj_tag(x_136) == 0)
{
lean_dec(x_137);
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
x_33 = x_9;
x_34 = x_138;
x_35 = lean_box(0);
goto block_73;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_136, 0);
lean_inc(x_139);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 x_140 = x_136;
} else {
 lean_dec_ref(x_136);
 x_140 = lean_box(0);
}
lean_inc(x_139);
x_141 = l_Lake_ArtifactDescr_fromJson_x3f(x_139);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_140);
lean_dec_ref(x_138);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
lean_dec_ref(x_141);
x_143 = l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__0;
x_144 = lean_unsigned_to_nat(80u);
x_145 = l_Lean_Json_pretty(x_139, x_144);
x_146 = lean_string_append(x_143, x_145);
lean_dec_ref(x_145);
x_147 = l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__1;
x_148 = lean_string_append(x_146, x_147);
x_149 = lean_string_append(x_148, x_142);
lean_dec(x_142);
x_74 = x_149;
x_75 = x_137;
x_76 = x_28;
x_77 = x_29;
x_78 = x_30;
x_79 = lean_box(0);
goto block_96;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_139);
x_150 = lean_ctor_get(x_9, 1);
x_151 = lean_ctor_get(x_141, 0);
lean_inc(x_151);
lean_dec_ref(x_141);
x_152 = lean_ctor_get(x_150, 2);
lean_inc_ref(x_152);
x_153 = l_Lake_Cache_getArtifact(x_152, x_151);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_137);
lean_dec_ref(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_9);
lean_dec_ref(x_4);
lean_dec(x_3);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
lean_dec_ref(x_153);
if (lean_is_scalar(x_140)) {
 x_155 = lean_alloc_ctor(1, 1, 0);
} else {
 x_155 = x_140;
}
lean_ctor_set(x_155, 0, x_154);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_138);
return x_156;
}
else
{
lean_object* x_157; 
lean_dec(x_140);
lean_dec_ref(x_138);
x_157 = lean_ctor_get(x_153, 0);
lean_inc(x_157);
lean_dec_ref(x_153);
x_74 = x_157;
x_75 = x_137;
x_76 = x_28;
x_77 = x_29;
x_78 = x_30;
x_79 = lean_box(0);
goto block_96;
}
}
}
}
}
else
{
uint8_t x_158; 
lean_dec_ref(x_32);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_9);
lean_dec_ref(x_4);
lean_dec(x_3);
x_158 = !lean_is_exclusive(x_97);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_97, 1);
x_160 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_29);
lean_ctor_set(x_160, 2, x_30);
lean_ctor_set_uint8(x_160, sizeof(void*)*3, x_28);
lean_ctor_set(x_97, 1, x_160);
return x_97;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_161 = lean_ctor_get(x_97, 0);
x_162 = lean_ctor_get(x_97, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_97);
x_163 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_29);
lean_ctor_set(x_163, 2, x_30);
lean_ctor_set_uint8(x_163, sizeof(void*)*3, x_28);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
block_22:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
block_73:
{
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_36; uint64_t x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_36);
lean_dec_ref(x_3);
x_37 = lean_ctor_get_uint64(x_36, sizeof(void*)*3);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec_ref(x_36);
x_39 = lean_uint64_dec_eq(x_37, x_2);
if (x_39 == 0)
{
lean_dec(x_38);
lean_dec_ref(x_33);
lean_dec_ref(x_32);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_4);
x_12 = x_34;
x_13 = lean_box(0);
goto block_16;
}
else
{
if (lean_obj_tag(x_38) == 0)
{
lean_dec_ref(x_33);
lean_dec_ref(x_32);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_4);
x_12 = x_34;
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec_ref(x_38);
lean_inc(x_40);
x_41 = l_Lake_ArtifactDescr_fromJson_x3f(x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_33);
lean_dec_ref(x_32);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_4);
x_12 = x_34;
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_33, 1);
lean_inc(x_42);
lean_dec_ref(x_33);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec_ref(x_41);
x_44 = lean_ctor_get(x_34, 0);
x_45 = lean_ctor_get_uint8(x_34, sizeof(void*)*3);
x_46 = lean_ctor_get(x_34, 1);
x_47 = lean_ctor_get(x_34, 2);
x_48 = lean_ctor_get(x_42, 2);
lean_inc_ref(x_48);
lean_dec(x_42);
x_49 = l_Lake_Cache_getArtifact(x_48, x_43);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = lean_unbox(x_25);
lean_dec(x_25);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_40);
lean_dec_ref(x_32);
lean_dec(x_26);
lean_dec_ref(x_4);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec_ref(x_49);
x_17 = x_51;
x_18 = x_34;
x_19 = lean_box(0);
goto block_22;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 0);
lean_inc(x_52);
lean_dec_ref(x_49);
x_53 = l_Lake_Cache_writeOutputsCore(x_4, x_32, x_2, x_40);
lean_dec_ref(x_32);
if (lean_obj_tag(x_53) == 0)
{
lean_dec_ref(x_53);
lean_dec(x_26);
x_17 = x_52;
x_18 = x_34;
x_19 = lean_box(0);
goto block_22;
}
else
{
uint8_t x_54; 
lean_dec(x_52);
lean_inc(x_47);
lean_inc_ref(x_46);
lean_inc_ref(x_44);
x_54 = !lean_is_exclusive(x_34);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_55 = lean_ctor_get(x_34, 2);
lean_dec(x_55);
x_56 = lean_ctor_get(x_34, 1);
lean_dec(x_56);
x_57 = lean_ctor_get(x_34, 0);
lean_dec(x_57);
x_58 = lean_ctor_get(x_53, 0);
lean_inc(x_58);
lean_dec_ref(x_53);
x_59 = lean_io_error_to_string(x_58);
x_60 = 3;
x_61 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_60);
x_62 = lean_array_get_size(x_44);
x_63 = lean_array_push(x_44, x_61);
lean_ctor_set(x_34, 0, x_63);
if (lean_is_scalar(x_26)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_26;
 lean_ctor_set_tag(x_64, 1);
}
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_34);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_34);
x_65 = lean_ctor_get(x_53, 0);
lean_inc(x_65);
lean_dec_ref(x_53);
x_66 = lean_io_error_to_string(x_65);
x_67 = 3;
x_68 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set_uint8(x_68, sizeof(void*)*1, x_67);
x_69 = lean_array_get_size(x_44);
x_70 = lean_array_push(x_44, x_68);
x_71 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_46);
lean_ctor_set(x_71, 2, x_47);
lean_ctor_set_uint8(x_71, sizeof(void*)*3, x_45);
if (lean_is_scalar(x_26)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_26;
 lean_ctor_set_tag(x_72, 1);
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
else
{
lean_dec_ref(x_49);
lean_dec(x_40);
lean_dec_ref(x_32);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_4);
x_12 = x_34;
x_13 = lean_box(0);
goto block_16;
}
}
}
}
}
else
{
lean_dec_ref(x_33);
lean_dec_ref(x_32);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_4);
lean_dec(x_3);
x_12 = x_34;
x_13 = lean_box(0);
goto block_16;
}
}
block_96:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_80 = l_Lake_getArtifacts_x3f___redArg___closed__0;
x_81 = l_Lake_Hash_hex(x_2);
x_82 = lean_unsigned_to_nat(7u);
x_83 = lean_unsigned_to_nat(0u);
x_84 = lean_string_utf8_byte_size(x_81);
lean_inc_ref(x_81);
x_85 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_85, 0, x_81);
lean_ctor_set(x_85, 1, x_83);
lean_ctor_set(x_85, 2, x_84);
x_86 = l_Substring_nextn(x_85, x_82, x_83);
lean_dec_ref(x_85);
x_87 = lean_string_utf8_extract(x_81, x_83, x_86);
lean_dec(x_86);
lean_dec_ref(x_81);
x_88 = lean_string_append(x_80, x_87);
lean_dec_ref(x_87);
x_89 = l_Lake_getArtifacts_x3f___redArg___closed__1;
x_90 = lean_string_append(x_88, x_89);
x_91 = lean_string_append(x_90, x_74);
lean_dec_ref(x_74);
x_92 = 2;
x_93 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set_uint8(x_93, sizeof(void*)*1, x_92);
x_94 = lean_array_push(x_75, x_93);
if (lean_is_scalar(x_31)) {
 x_95 = lean_alloc_ctor(0, 3, 1);
} else {
 x_95 = x_31;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_77);
lean_ctor_set(x_95, 2, x_78);
lean_ctor_set_uint8(x_95, sizeof(void*)*3, x_76);
x_33 = x_9;
x_34 = x_95;
x_35 = lean_box(0);
goto block_73;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 2);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_dec(x_13);
lean_inc_ref(x_2);
lean_ctor_set(x_1, 2, x_2);
lean_ctor_set(x_1, 1, x_2);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 3);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_1);
lean_inc_ref(x_2);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_2);
lean_ctor_set(x_18, 2, x_2);
lean_ctor_set(x_18, 3, x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_9);
return x_20;
}
}
}
static lean_object* _init_l_Lake_buildArtifactUnlessUpToDate___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("restored artifact from cache to: ", 33, 33);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1(uint64_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
lean_inc_ref(x_13);
lean_inc(x_2);
x_16 = l_Lake_getArtifacts_x3f___at___Lake_buildArtifactUnlessUpToDate_spec__1(x_9, x_1, x_2, x_3, x_4, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_dec_ref(x_13);
lean_dec_ref(x_5);
lean_dec(x_2);
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_148; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_19 = x_16;
} else {
 lean_dec_ref(x_16);
 x_19 = lean_box(0);
}
x_20 = lean_ctor_get(x_17, 0);
x_21 = l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(x_1, x_2, x_18);
lean_dec(x_2);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_24 = x_21;
} else {
 lean_dec_ref(x_21);
 x_24 = lean_box(0);
}
x_148 = lean_unbox(x_22);
lean_dec(x_22);
if (x_148 == 0)
{
lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_149 = lean_ctor_get(x_23, 0);
x_150 = lean_ctor_get_uint8(x_23, sizeof(void*)*3);
x_151 = lean_ctor_get(x_23, 1);
x_152 = lean_ctor_get(x_23, 2);
x_153 = l_Lake_removeFileIfExists(x_5);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_179; uint64_t x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 x_154 = x_153;
} else {
 lean_dec_ref(x_153);
 x_154 = lean_box(0);
}
x_179 = lean_ctor_get(x_20, 0);
x_180 = lean_ctor_get_uint64(x_179, sizeof(void*)*1);
x_181 = lean_ctor_get(x_179, 0);
x_182 = lean_string_utf8_byte_size(x_181);
x_183 = lean_unsigned_to_nat(0u);
x_184 = lean_nat_dec_eq(x_182, x_183);
lean_dec(x_182);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_185 = l_Lake_Hash_hex(x_180);
x_186 = l_Lake_instToOutputJsonArtifact___lam__0___closed__0;
x_187 = lean_string_append(x_185, x_186);
x_188 = lean_string_append(x_187, x_181);
x_155 = x_188;
goto block_178;
}
else
{
lean_object* x_189; 
x_189 = l_Lake_Hash_hex(x_180);
x_155 = x_189;
goto block_178;
}
block_178:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
if (lean_is_scalar(x_154)) {
 x_156 = lean_alloc_ctor(3, 1, 0);
} else {
 x_156 = x_154;
 lean_ctor_set_tag(x_156, 3);
}
lean_ctor_set(x_156, 0, x_155);
x_157 = l_Lake_BuildMetadata_ofFetch(x_1, x_156);
x_158 = l_Lake_BuildMetadata_writeFile(x_7, x_157);
if (lean_obj_tag(x_158) == 0)
{
lean_dec_ref(x_158);
x_61 = x_9;
x_62 = x_10;
x_63 = x_11;
x_64 = x_12;
x_65 = x_13;
x_66 = x_23;
x_67 = lean_box(0);
goto block_147;
}
else
{
uint8_t x_159; 
lean_inc(x_152);
lean_inc_ref(x_151);
lean_inc_ref(x_149);
lean_dec(x_24);
lean_dec(x_19);
lean_dec_ref(x_17);
lean_dec_ref(x_13);
lean_dec_ref(x_5);
x_159 = !lean_is_exclusive(x_23);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_160 = lean_ctor_get(x_23, 2);
lean_dec(x_160);
x_161 = lean_ctor_get(x_23, 1);
lean_dec(x_161);
x_162 = lean_ctor_get(x_23, 0);
lean_dec(x_162);
x_163 = lean_ctor_get(x_158, 0);
lean_inc(x_163);
lean_dec_ref(x_158);
x_164 = lean_io_error_to_string(x_163);
x_165 = 3;
x_166 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set_uint8(x_166, sizeof(void*)*1, x_165);
x_167 = lean_array_get_size(x_149);
x_168 = lean_array_push(x_149, x_166);
lean_ctor_set(x_23, 0, x_168);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_23);
return x_169;
}
else
{
lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_23);
x_170 = lean_ctor_get(x_158, 0);
lean_inc(x_170);
lean_dec_ref(x_158);
x_171 = lean_io_error_to_string(x_170);
x_172 = 3;
x_173 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set_uint8(x_173, sizeof(void*)*1, x_172);
x_174 = lean_array_get_size(x_149);
x_175 = lean_array_push(x_149, x_173);
x_176 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_151);
lean_ctor_set(x_176, 2, x_152);
lean_ctor_set_uint8(x_176, sizeof(void*)*3, x_150);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
}
else
{
uint8_t x_190; 
lean_inc(x_152);
lean_inc_ref(x_151);
lean_inc_ref(x_149);
lean_dec(x_24);
lean_dec(x_19);
lean_dec_ref(x_17);
lean_dec_ref(x_13);
lean_dec_ref(x_5);
x_190 = !lean_is_exclusive(x_23);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_191 = lean_ctor_get(x_23, 2);
lean_dec(x_191);
x_192 = lean_ctor_get(x_23, 1);
lean_dec(x_192);
x_193 = lean_ctor_get(x_23, 0);
lean_dec(x_193);
x_194 = lean_ctor_get(x_153, 0);
lean_inc(x_194);
lean_dec_ref(x_153);
x_195 = lean_io_error_to_string(x_194);
x_196 = 3;
x_197 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set_uint8(x_197, sizeof(void*)*1, x_196);
x_198 = lean_array_get_size(x_149);
x_199 = lean_array_push(x_149, x_197);
lean_ctor_set(x_23, 0, x_199);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_23);
return x_200;
}
else
{
lean_object* x_201; lean_object* x_202; uint8_t x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_23);
x_201 = lean_ctor_get(x_153, 0);
lean_inc(x_201);
lean_dec_ref(x_153);
x_202 = lean_io_error_to_string(x_201);
x_203 = 3;
x_204 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set_uint8(x_204, sizeof(void*)*1, x_203);
x_205 = lean_array_get_size(x_149);
x_206 = lean_array_push(x_149, x_204);
x_207 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_151);
lean_ctor_set(x_207, 2, x_152);
lean_ctor_set_uint8(x_207, sizeof(void*)*3, x_150);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
else
{
x_61 = x_9;
x_62 = x_10;
x_63 = x_11;
x_64 = x_12;
x_65 = x_13;
x_66 = x_23;
x_67 = lean_box(0);
goto block_147;
}
block_60:
{
lean_object* x_32; uint64_t x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_20, 0);
x_33 = lean_ctor_get_uint64(x_32, sizeof(void*)*1);
x_34 = lean_ctor_get(x_30, 0);
x_35 = lean_ctor_get_uint8(x_30, sizeof(void*)*3);
x_36 = lean_ctor_get(x_30, 1);
x_37 = lean_ctor_get(x_30, 2);
lean_inc_ref(x_5);
x_38 = l_Lake_writeFileHash(x_5, x_33);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_24);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
x_40 = l_Lake_buildArtifactUnlessUpToDate___lam__0(x_20, x_5, x_39, x_25, x_26, x_27, x_28, x_29, x_30);
lean_dec_ref(x_29);
return x_40;
}
else
{
uint8_t x_41; 
lean_inc(x_37);
lean_inc_ref(x_36);
lean_inc_ref(x_34);
lean_dec_ref(x_29);
lean_dec(x_20);
lean_dec_ref(x_5);
x_41 = !lean_is_exclusive(x_30);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_42 = lean_ctor_get(x_30, 2);
lean_dec(x_42);
x_43 = lean_ctor_get(x_30, 1);
lean_dec(x_43);
x_44 = lean_ctor_get(x_30, 0);
lean_dec(x_44);
x_45 = lean_ctor_get(x_38, 0);
lean_inc(x_45);
lean_dec_ref(x_38);
x_46 = lean_io_error_to_string(x_45);
x_47 = 3;
x_48 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_47);
x_49 = lean_array_get_size(x_34);
x_50 = lean_array_push(x_34, x_48);
lean_ctor_set(x_30, 0, x_50);
if (lean_is_scalar(x_24)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_24;
 lean_ctor_set_tag(x_51, 1);
}
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_30);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_30);
x_52 = lean_ctor_get(x_38, 0);
lean_inc(x_52);
lean_dec_ref(x_38);
x_53 = lean_io_error_to_string(x_52);
x_54 = 3;
x_55 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_54);
x_56 = lean_array_get_size(x_34);
x_57 = lean_array_push(x_34, x_55);
x_58 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_36);
lean_ctor_set(x_58, 2, x_37);
lean_ctor_set_uint8(x_58, sizeof(void*)*3, x_35);
if (lean_is_scalar(x_24)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_24;
 lean_ctor_set_tag(x_59, 1);
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
block_147:
{
if (x_8 == 0)
{
lean_object* x_68; 
lean_dec_ref(x_65);
lean_dec(x_24);
lean_dec_ref(x_5);
if (lean_is_scalar(x_19)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_19;
}
lean_ctor_set(x_68, 0, x_17);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
else
{
uint8_t x_69; 
lean_inc(x_20);
lean_dec_ref(x_17);
x_69 = l_System_FilePath_pathExists(x_5);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_66);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_71 = lean_ctor_get(x_66, 0);
x_72 = l_Lake_buildArtifactUnlessUpToDate___lam__1___closed__0;
x_73 = lean_string_append(x_72, x_5);
x_74 = 0;
x_75 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set_uint8(x_75, sizeof(void*)*1, x_74);
x_76 = lean_array_push(x_71, x_75);
x_77 = l_Lake_createParentDirs(x_5);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec_ref(x_77);
x_78 = lean_ctor_get(x_20, 1);
x_79 = l_Lake_copyFile(x_78, x_5);
if (lean_obj_tag(x_79) == 0)
{
lean_dec_ref(x_79);
if (x_6 == 0)
{
lean_dec(x_19);
lean_ctor_set(x_66, 0, x_76);
x_25 = x_61;
x_26 = x_62;
x_27 = x_63;
x_28 = x_64;
x_29 = x_65;
x_30 = x_66;
x_31 = lean_box(0);
goto block_60;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_80, 0, x_6);
lean_ctor_set_uint8(x_80, 1, x_6);
lean_ctor_set_uint8(x_80, 2, x_6);
lean_inc_ref_n(x_80, 2);
x_81 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_80);
lean_ctor_set(x_81, 2, x_80);
x_82 = l_IO_setAccessRights(x_5, x_81);
lean_dec_ref(x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_dec_ref(x_82);
lean_dec(x_19);
lean_ctor_set(x_66, 0, x_76);
x_25 = x_61;
x_26 = x_62;
x_27 = x_63;
x_28 = x_64;
x_29 = x_65;
x_30 = x_66;
x_31 = lean_box(0);
goto block_60;
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec_ref(x_65);
lean_dec(x_24);
lean_dec(x_20);
lean_dec_ref(x_5);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
x_84 = lean_io_error_to_string(x_83);
x_85 = 3;
x_86 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set_uint8(x_86, sizeof(void*)*1, x_85);
x_87 = lean_array_get_size(x_76);
x_88 = lean_array_push(x_76, x_86);
lean_ctor_set(x_66, 0, x_88);
if (lean_is_scalar(x_19)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_19;
 lean_ctor_set_tag(x_89, 1);
}
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_66);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec_ref(x_65);
lean_dec(x_24);
lean_dec(x_20);
lean_dec_ref(x_5);
x_90 = lean_ctor_get(x_79, 0);
lean_inc(x_90);
lean_dec_ref(x_79);
x_91 = lean_io_error_to_string(x_90);
x_92 = 3;
x_93 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set_uint8(x_93, sizeof(void*)*1, x_92);
x_94 = lean_array_get_size(x_76);
x_95 = lean_array_push(x_76, x_93);
lean_ctor_set(x_66, 0, x_95);
if (lean_is_scalar(x_19)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_19;
 lean_ctor_set_tag(x_96, 1);
}
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_66);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec_ref(x_65);
lean_dec(x_24);
lean_dec(x_20);
lean_dec_ref(x_5);
x_97 = lean_ctor_get(x_77, 0);
lean_inc(x_97);
lean_dec_ref(x_77);
x_98 = lean_io_error_to_string(x_97);
x_99 = 3;
x_100 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set_uint8(x_100, sizeof(void*)*1, x_99);
x_101 = lean_array_get_size(x_76);
x_102 = lean_array_push(x_76, x_100);
lean_ctor_set(x_66, 0, x_102);
if (lean_is_scalar(x_19)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_19;
 lean_ctor_set_tag(x_103, 1);
}
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_66);
return x_103;
}
}
else
{
lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_104 = lean_ctor_get(x_66, 0);
x_105 = lean_ctor_get_uint8(x_66, sizeof(void*)*3);
x_106 = lean_ctor_get(x_66, 1);
x_107 = lean_ctor_get(x_66, 2);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_104);
lean_dec(x_66);
x_108 = l_Lake_buildArtifactUnlessUpToDate___lam__1___closed__0;
x_109 = lean_string_append(x_108, x_5);
x_110 = 0;
x_111 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set_uint8(x_111, sizeof(void*)*1, x_110);
x_112 = lean_array_push(x_104, x_111);
x_113 = l_Lake_createParentDirs(x_5);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; 
lean_dec_ref(x_113);
x_114 = lean_ctor_get(x_20, 1);
x_115 = l_Lake_copyFile(x_114, x_5);
if (lean_obj_tag(x_115) == 0)
{
lean_dec_ref(x_115);
if (x_6 == 0)
{
lean_object* x_116; 
lean_dec(x_19);
x_116 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_116, 0, x_112);
lean_ctor_set(x_116, 1, x_106);
lean_ctor_set(x_116, 2, x_107);
lean_ctor_set_uint8(x_116, sizeof(void*)*3, x_105);
x_25 = x_61;
x_26 = x_62;
x_27 = x_63;
x_28 = x_64;
x_29 = x_65;
x_30 = x_116;
x_31 = lean_box(0);
goto block_60;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_117, 0, x_6);
lean_ctor_set_uint8(x_117, 1, x_6);
lean_ctor_set_uint8(x_117, 2, x_6);
lean_inc_ref_n(x_117, 2);
x_118 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_117);
lean_ctor_set(x_118, 2, x_117);
x_119 = l_IO_setAccessRights(x_5, x_118);
lean_dec_ref(x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; 
lean_dec_ref(x_119);
lean_dec(x_19);
x_120 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_120, 0, x_112);
lean_ctor_set(x_120, 1, x_106);
lean_ctor_set(x_120, 2, x_107);
lean_ctor_set_uint8(x_120, sizeof(void*)*3, x_105);
x_25 = x_61;
x_26 = x_62;
x_27 = x_63;
x_28 = x_64;
x_29 = x_65;
x_30 = x_120;
x_31 = lean_box(0);
goto block_60;
}
else
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec_ref(x_65);
lean_dec(x_24);
lean_dec(x_20);
lean_dec_ref(x_5);
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
lean_dec_ref(x_119);
x_122 = lean_io_error_to_string(x_121);
x_123 = 3;
x_124 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set_uint8(x_124, sizeof(void*)*1, x_123);
x_125 = lean_array_get_size(x_112);
x_126 = lean_array_push(x_112, x_124);
x_127 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_106);
lean_ctor_set(x_127, 2, x_107);
lean_ctor_set_uint8(x_127, sizeof(void*)*3, x_105);
if (lean_is_scalar(x_19)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_19;
 lean_ctor_set_tag(x_128, 1);
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec_ref(x_65);
lean_dec(x_24);
lean_dec(x_20);
lean_dec_ref(x_5);
x_129 = lean_ctor_get(x_115, 0);
lean_inc(x_129);
lean_dec_ref(x_115);
x_130 = lean_io_error_to_string(x_129);
x_131 = 3;
x_132 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set_uint8(x_132, sizeof(void*)*1, x_131);
x_133 = lean_array_get_size(x_112);
x_134 = lean_array_push(x_112, x_132);
x_135 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_106);
lean_ctor_set(x_135, 2, x_107);
lean_ctor_set_uint8(x_135, sizeof(void*)*3, x_105);
if (lean_is_scalar(x_19)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_19;
 lean_ctor_set_tag(x_136, 1);
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec_ref(x_65);
lean_dec(x_24);
lean_dec(x_20);
lean_dec_ref(x_5);
x_137 = lean_ctor_get(x_113, 0);
lean_inc(x_137);
lean_dec_ref(x_113);
x_138 = lean_io_error_to_string(x_137);
x_139 = 3;
x_140 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set_uint8(x_140, sizeof(void*)*1, x_139);
x_141 = lean_array_get_size(x_112);
x_142 = lean_array_push(x_112, x_140);
x_143 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_106);
lean_ctor_set(x_143, 2, x_107);
lean_ctor_set_uint8(x_143, sizeof(void*)*3, x_105);
if (lean_is_scalar(x_19)) {
 x_144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_144 = x_19;
 lean_ctor_set_tag(x_144, 1);
}
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
else
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_24);
lean_dec(x_19);
x_145 = lean_box(0);
x_146 = l_Lake_buildArtifactUnlessUpToDate___lam__0(x_20, x_5, x_145, x_61, x_62, x_63, x_64, x_65, x_66);
lean_dec_ref(x_65);
return x_146;
}
}
}
}
}
else
{
lean_dec_ref(x_13);
lean_dec_ref(x_5);
lean_dec(x_2);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, uint64_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_18; uint8_t x_19; 
x_18 = 1;
x_19 = l_Lake_instDecidableEqOutputStatus(x_1, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec_ref(x_15);
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get_uint8(x_16, sizeof(void*)*3);
x_23 = lean_ctor_get(x_16, 1);
x_24 = lean_ctor_get(x_16, 2);
x_25 = lean_ctor_get(x_20, 2);
lean_inc_ref(x_25);
lean_dec(x_20);
x_26 = l_Lake_Cache_saveArtifact(x_25, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint64_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get_uint64(x_29, sizeof(void*)*1);
x_31 = lean_ctor_get(x_29, 0);
x_32 = l_Lake_Package_cacheScope(x_7);
x_57 = lean_string_utf8_byte_size(x_31);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_nat_dec_eq(x_57, x_58);
lean_dec(x_57);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = l_Lake_Hash_hex(x_30);
x_61 = l_Lake_instToOutputJsonArtifact___lam__0___closed__0;
x_62 = lean_string_append(x_60, x_61);
x_63 = lean_string_append(x_62, x_31);
x_33 = x_63;
goto block_56;
}
else
{
lean_object* x_64; 
x_64 = l_Lake_Hash_hex(x_30);
x_33 = x_64;
goto block_56;
}
block_56:
{
lean_object* x_34; lean_object* x_35; 
if (lean_is_scalar(x_28)) {
 x_34 = lean_alloc_ctor(3, 1, 0);
} else {
 x_34 = x_28;
 lean_ctor_set_tag(x_34, 3);
}
lean_ctor_set(x_34, 0, x_33);
x_35 = l_Lake_Cache_writeOutputsCore(x_8, x_32, x_9, x_34);
lean_dec_ref(x_32);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
lean_dec_ref(x_35);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_27);
lean_ctor_set(x_36, 1, x_16);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_27);
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc_ref(x_21);
x_37 = !lean_is_exclusive(x_16);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_38 = lean_ctor_get(x_16, 2);
lean_dec(x_38);
x_39 = lean_ctor_get(x_16, 1);
lean_dec(x_39);
x_40 = lean_ctor_get(x_16, 0);
lean_dec(x_40);
x_41 = lean_ctor_get(x_35, 0);
lean_inc(x_41);
lean_dec_ref(x_35);
x_42 = lean_io_error_to_string(x_41);
x_43 = 3;
x_44 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_43);
x_45 = lean_array_get_size(x_21);
x_46 = lean_array_push(x_21, x_44);
lean_ctor_set(x_16, 0, x_46);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_16);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_16);
x_48 = lean_ctor_get(x_35, 0);
lean_inc(x_48);
lean_dec_ref(x_35);
x_49 = lean_io_error_to_string(x_48);
x_50 = 3;
x_51 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_50);
x_52 = lean_array_get_size(x_21);
x_53 = lean_array_push(x_21, x_51);
x_54 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_23);
lean_ctor_set(x_54, 2, x_24);
lean_ctor_set_uint8(x_54, sizeof(void*)*3, x_22);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
else
{
uint8_t x_65; 
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc_ref(x_21);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_65 = !lean_is_exclusive(x_16);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_66 = lean_ctor_get(x_16, 2);
lean_dec(x_66);
x_67 = lean_ctor_get(x_16, 1);
lean_dec(x_67);
x_68 = lean_ctor_get(x_16, 0);
lean_dec(x_68);
x_69 = lean_ctor_get(x_26, 0);
lean_inc(x_69);
lean_dec_ref(x_26);
x_70 = lean_io_error_to_string(x_69);
x_71 = 3;
x_72 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set_uint8(x_72, sizeof(void*)*1, x_71);
x_73 = lean_array_get_size(x_21);
x_74 = lean_array_push(x_21, x_72);
lean_ctor_set(x_16, 0, x_74);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_16);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_16);
x_76 = lean_ctor_get(x_26, 0);
lean_inc(x_76);
lean_dec_ref(x_26);
x_77 = lean_io_error_to_string(x_76);
x_78 = 3;
x_79 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set_uint8(x_79, sizeof(void*)*1, x_78);
x_80 = lean_array_get_size(x_21);
x_81 = lean_array_push(x_21, x_79);
x_82 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_23);
lean_ctor_set(x_82, 2, x_24);
lean_ctor_set_uint8(x_82, sizeof(void*)*3, x_22);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; 
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_84 = l_Lake_computeArtifact___redArg(x_2, x_3, x_4, x_15, x_16);
lean_dec_ref(x_15);
return x_84;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; uint8_t x_37; 
x_37 = !lean_is_exclusive(x_12);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_12, 0);
x_39 = lean_ctor_get(x_12, 1);
x_40 = l_Lake_buildFileUnlessUpToDate_x27___closed__0;
lean_inc_ref(x_1);
x_41 = lean_string_append(x_1, x_40);
lean_inc_ref(x_41);
x_42 = l_Lake_readTraceFile(x_41, x_38);
if (lean_obj_tag(x_42) == 0)
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
x_45 = lean_ctor_get(x_39, 2);
lean_inc_ref(x_39);
lean_ctor_set(x_12, 0, x_44);
x_46 = l_Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0(x_7, x_1, x_39, x_43, x_45, x_8, x_9, x_10, x_11, x_12);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
x_49 = 0;
x_50 = lean_unbox(x_47);
lean_dec(x_47);
x_51 = l_Lake_instDecidableEqOutputStatus(x_50, x_49);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec_ref(x_41);
lean_dec_ref(x_39);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_52 = l_Lake_computeArtifact___redArg(x_1, x_4, x_3, x_11, x_48);
lean_dec_ref(x_11);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec_ref(x_52);
x_14 = x_53;
x_15 = x_54;
x_16 = lean_box(0);
goto block_27;
}
else
{
return x_52;
}
}
else
{
lean_object* x_55; 
x_55 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_4, x_39, x_41, x_7, x_8, x_9, x_10, x_11, x_48);
lean_dec_ref(x_41);
lean_dec_ref(x_39);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec_ref(x_55);
x_14 = x_56;
x_15 = x_57;
x_16 = lean_box(0);
goto block_27;
}
else
{
return x_55;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint64_t x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_106; uint8_t x_110; uint8_t x_135; uint8_t x_136; 
x_58 = lean_ctor_get(x_42, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_42, 1);
lean_inc(x_59);
lean_dec_ref(x_42);
x_60 = lean_ctor_get(x_8, 0);
lean_inc(x_60);
lean_inc_ref(x_39);
lean_ctor_set(x_12, 0, x_59);
x_61 = l_Lake_Package_isArtifactCacheEnabled___at___Lake_buildArtifactUnlessUpToDate_spec__0___redArg(x_60, x_11, x_12);
x_62 = lean_ctor_get(x_11, 1);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec_ref(x_61);
x_65 = lean_ctor_get(x_62, 2);
x_66 = lean_ctor_get_uint64(x_39, sizeof(void*)*3);
x_67 = lean_ctor_get(x_39, 2);
x_135 = 1;
x_136 = lean_unbox(x_63);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; uint8_t x_141; uint8_t x_142; 
lean_inc(x_58);
x_137 = l_Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0(x_7, x_1, x_39, x_58, x_67, x_8, x_9, x_10, x_11, x_64);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec_ref(x_137);
x_140 = 0;
x_141 = lean_unbox(x_138);
lean_dec(x_138);
x_142 = l_Lake_instDecidableEqOutputStatus(x_141, x_140);
if (x_142 == 0)
{
uint8_t x_143; lean_object* x_144; 
lean_dec(x_58);
lean_dec_ref(x_41);
lean_dec_ref(x_39);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_143 = lean_unbox(x_63);
lean_dec(x_63);
x_144 = l_Lake_computeArtifact___redArg(x_1, x_4, x_143, x_11, x_139);
lean_dec_ref(x_11);
x_106 = x_144;
goto block_109;
}
else
{
lean_object* x_145; 
lean_dec(x_63);
lean_inc_ref(x_11);
lean_inc_ref(x_1);
lean_inc(x_60);
lean_inc_ref(x_65);
x_145 = l_Lake_buildArtifactUnlessUpToDate___lam__1(x_66, x_58, x_65, x_60, x_1, x_6, x_41, x_135, x_7, x_8, x_9, x_10, x_11, x_139);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec_ref(x_145);
x_148 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_4, x_39, x_41, x_7, x_8, x_9, x_10, x_11, x_147);
lean_dec_ref(x_41);
lean_dec_ref(x_39);
x_106 = x_148;
goto block_109;
}
else
{
lean_object* x_149; lean_object* x_150; 
lean_dec_ref(x_41);
lean_dec_ref(x_39);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_149 = lean_ctor_get(x_145, 1);
lean_inc(x_149);
lean_dec_ref(x_145);
x_150 = lean_ctor_get(x_146, 0);
lean_inc(x_150);
lean_dec_ref(x_146);
x_81 = x_150;
x_82 = x_149;
x_83 = lean_box(0);
goto block_105;
}
}
else
{
uint8_t x_151; 
lean_dec(x_60);
lean_dec_ref(x_41);
lean_dec_ref(x_39);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_151 = !lean_is_exclusive(x_145);
if (x_151 == 0)
{
return x_145;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_145, 0);
x_153 = lean_ctor_get(x_145, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_145);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
}
else
{
lean_inc_ref(x_65);
lean_dec(x_63);
if (x_5 == 0)
{
lean_object* x_155; uint8_t x_156; 
x_155 = lean_ctor_get(x_60, 4);
x_156 = lean_ctor_get_uint8(x_155, sizeof(void*)*26 + 4);
x_110 = x_156;
goto block_134;
}
else
{
x_110 = x_135;
goto block_134;
}
}
block_80:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec_ref(x_69);
x_77 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_78 = l_Lake_CacheMap_insertCore(x_66, x_77, x_74);
x_79 = lean_st_ref_set(x_72, x_78);
lean_dec(x_72);
x_28 = x_70;
x_29 = x_71;
x_30 = x_68;
x_31 = x_75;
x_32 = lean_box(0);
goto block_36;
}
block_105:
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_60, 21);
lean_inc(x_84);
lean_dec(x_60);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; uint8_t x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_82, 0);
lean_inc_ref(x_85);
x_86 = lean_ctor_get_uint8(x_82, sizeof(void*)*3);
x_87 = lean_ctor_get(x_82, 2);
lean_inc(x_87);
lean_dec_ref(x_82);
x_28 = x_81;
x_29 = x_85;
x_30 = x_86;
x_31 = x_87;
x_32 = lean_box(0);
goto block_36;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; uint64_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_88 = lean_ctor_get(x_84, 0);
lean_inc(x_88);
lean_dec_ref(x_84);
x_89 = lean_st_ref_take(x_88);
x_90 = lean_ctor_get(x_81, 0);
x_91 = lean_ctor_get(x_82, 0);
lean_inc_ref(x_91);
x_92 = lean_ctor_get_uint8(x_82, sizeof(void*)*3);
x_93 = lean_ctor_get(x_82, 1);
lean_inc_ref(x_93);
x_94 = lean_ctor_get(x_82, 2);
lean_inc(x_94);
lean_dec_ref(x_82);
x_95 = lean_ctor_get_uint64(x_90, sizeof(void*)*1);
x_96 = lean_ctor_get(x_90, 0);
x_97 = lean_string_utf8_byte_size(x_96);
x_98 = lean_unsigned_to_nat(0u);
x_99 = lean_nat_dec_eq(x_97, x_98);
lean_dec(x_97);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = l_Lake_Hash_hex(x_95);
x_101 = l_Lake_instToOutputJsonArtifact___lam__0___closed__0;
x_102 = lean_string_append(x_100, x_101);
x_103 = lean_string_append(x_102, x_96);
x_68 = x_92;
x_69 = x_93;
x_70 = x_81;
x_71 = x_91;
x_72 = x_88;
x_73 = lean_box(0);
x_74 = x_89;
x_75 = x_94;
x_76 = x_103;
goto block_80;
}
else
{
lean_object* x_104; 
x_104 = l_Lake_Hash_hex(x_95);
x_68 = x_92;
x_69 = x_93;
x_70 = x_81;
x_71 = x_91;
x_72 = x_88;
x_73 = lean_box(0);
x_74 = x_89;
x_75 = x_94;
x_76 = x_104;
goto block_80;
}
}
}
block_109:
{
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec_ref(x_106);
x_81 = x_107;
x_82 = x_108;
x_83 = lean_box(0);
goto block_105;
}
else
{
lean_dec(x_60);
return x_106;
}
}
block_134:
{
lean_object* x_111; 
lean_inc_ref(x_11);
lean_inc_ref(x_1);
lean_inc(x_60);
lean_inc_ref(x_65);
lean_inc(x_58);
x_111 = l_Lake_buildArtifactUnlessUpToDate___lam__1(x_66, x_58, x_65, x_60, x_1, x_6, x_41, x_110, x_7, x_8, x_9, x_10, x_11, x_64);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; 
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec_ref(x_111);
x_114 = l_Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0(x_7, x_1, x_39, x_58, x_67, x_8, x_9, x_10, x_11, x_113);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec_ref(x_114);
x_117 = 0;
x_118 = lean_unbox(x_115);
x_119 = l_Lake_instDecidableEqOutputStatus(x_118, x_117);
if (x_119 == 0)
{
lean_object* x_120; uint8_t x_121; lean_object* x_122; 
lean_dec_ref(x_41);
lean_dec_ref(x_39);
lean_dec_ref(x_2);
x_120 = lean_box(0);
x_121 = lean_unbox(x_115);
lean_dec(x_115);
lean_inc(x_60);
x_122 = l_Lake_buildArtifactUnlessUpToDate___lam__2(x_121, x_1, x_4, x_3, x_6, x_110, x_60, x_65, x_66, x_120, x_7, x_8, x_9, x_10, x_11, x_116);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_106 = x_122;
goto block_109;
}
else
{
lean_object* x_123; 
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_4);
lean_inc_ref(x_1);
x_123 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_4, x_39, x_41, x_7, x_8, x_9, x_10, x_11, x_116);
lean_dec_ref(x_41);
lean_dec_ref(x_39);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
lean_dec_ref(x_123);
x_125 = lean_box(0);
x_126 = lean_unbox(x_115);
lean_dec(x_115);
lean_inc(x_60);
x_127 = l_Lake_buildArtifactUnlessUpToDate___lam__2(x_126, x_1, x_4, x_3, x_6, x_110, x_60, x_65, x_66, x_125, x_7, x_8, x_9, x_10, x_11, x_124);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_106 = x_127;
goto block_109;
}
else
{
lean_dec(x_115);
lean_dec_ref(x_65);
lean_dec(x_60);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_123;
}
}
}
else
{
lean_object* x_128; lean_object* x_129; 
lean_dec_ref(x_65);
lean_dec(x_58);
lean_dec_ref(x_41);
lean_dec_ref(x_39);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_128 = lean_ctor_get(x_111, 1);
lean_inc(x_128);
lean_dec_ref(x_111);
x_129 = lean_ctor_get(x_112, 0);
lean_inc(x_129);
lean_dec_ref(x_112);
x_81 = x_129;
x_82 = x_128;
x_83 = lean_box(0);
goto block_105;
}
}
else
{
uint8_t x_130; 
lean_dec_ref(x_65);
lean_dec(x_60);
lean_dec(x_58);
lean_dec_ref(x_41);
lean_dec_ref(x_39);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_130 = !lean_is_exclusive(x_111);
if (x_130 == 0)
{
return x_111;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_111, 0);
x_132 = lean_ctor_get(x_111, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_111);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
}
}
else
{
uint8_t x_157; 
lean_dec_ref(x_41);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_157 = !lean_is_exclusive(x_42);
if (x_157 == 0)
{
lean_object* x_158; 
x_158 = lean_ctor_get(x_42, 1);
lean_ctor_set(x_12, 0, x_158);
lean_ctor_set(x_42, 1, x_12);
return x_42;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_42, 0);
x_160 = lean_ctor_get(x_42, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_42);
lean_ctor_set(x_12, 0, x_160);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_12);
return x_161;
}
}
}
else
{
lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_162 = lean_ctor_get(x_12, 0);
x_163 = lean_ctor_get_uint8(x_12, sizeof(void*)*3);
x_164 = lean_ctor_get(x_12, 1);
x_165 = lean_ctor_get(x_12, 2);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_162);
lean_dec(x_12);
x_166 = l_Lake_buildFileUnlessUpToDate_x27___closed__0;
lean_inc_ref(x_1);
x_167 = lean_string_append(x_1, x_166);
lean_inc_ref(x_167);
x_168 = l_Lake_readTraceFile(x_167, x_162);
if (lean_obj_tag(x_168) == 0)
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; uint8_t x_177; uint8_t x_178; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec_ref(x_168);
x_171 = lean_ctor_get(x_164, 2);
lean_inc_ref(x_164);
x_172 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_164);
lean_ctor_set(x_172, 2, x_165);
lean_ctor_set_uint8(x_172, sizeof(void*)*3, x_163);
x_173 = l_Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0(x_7, x_1, x_164, x_169, x_171, x_8, x_9, x_10, x_11, x_172);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec_ref(x_173);
x_176 = 0;
x_177 = lean_unbox(x_174);
lean_dec(x_174);
x_178 = l_Lake_instDecidableEqOutputStatus(x_177, x_176);
if (x_178 == 0)
{
lean_object* x_179; 
lean_dec_ref(x_167);
lean_dec_ref(x_164);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_179 = l_Lake_computeArtifact___redArg(x_1, x_4, x_3, x_11, x_175);
lean_dec_ref(x_11);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec_ref(x_179);
x_14 = x_180;
x_15 = x_181;
x_16 = lean_box(0);
goto block_27;
}
else
{
return x_179;
}
}
else
{
lean_object* x_182; 
x_182 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_4, x_164, x_167, x_7, x_8, x_9, x_10, x_11, x_175);
lean_dec_ref(x_167);
lean_dec_ref(x_164);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec_ref(x_182);
x_14 = x_183;
x_15 = x_184;
x_16 = lean_box(0);
goto block_27;
}
else
{
return x_182;
}
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint64_t x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_234; uint8_t x_238; uint8_t x_263; uint8_t x_264; 
x_185 = lean_ctor_get(x_168, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_168, 1);
lean_inc(x_186);
lean_dec_ref(x_168);
x_187 = lean_ctor_get(x_8, 0);
lean_inc(x_187);
lean_inc_ref(x_164);
x_188 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_164);
lean_ctor_set(x_188, 2, x_165);
lean_ctor_set_uint8(x_188, sizeof(void*)*3, x_163);
x_189 = l_Lake_Package_isArtifactCacheEnabled___at___Lake_buildArtifactUnlessUpToDate_spec__0___redArg(x_187, x_11, x_188);
x_190 = lean_ctor_get(x_11, 1);
x_191 = lean_ctor_get(x_189, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_189, 1);
lean_inc(x_192);
lean_dec_ref(x_189);
x_193 = lean_ctor_get(x_190, 2);
x_194 = lean_ctor_get_uint64(x_164, sizeof(void*)*3);
x_195 = lean_ctor_get(x_164, 2);
x_263 = 1;
x_264 = lean_unbox(x_191);
if (x_264 == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; uint8_t x_269; uint8_t x_270; 
lean_inc(x_185);
x_265 = l_Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0(x_7, x_1, x_164, x_185, x_195, x_8, x_9, x_10, x_11, x_192);
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
lean_dec_ref(x_265);
x_268 = 0;
x_269 = lean_unbox(x_266);
lean_dec(x_266);
x_270 = l_Lake_instDecidableEqOutputStatus(x_269, x_268);
if (x_270 == 0)
{
uint8_t x_271; lean_object* x_272; 
lean_dec(x_185);
lean_dec_ref(x_167);
lean_dec_ref(x_164);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_271 = lean_unbox(x_191);
lean_dec(x_191);
x_272 = l_Lake_computeArtifact___redArg(x_1, x_4, x_271, x_11, x_267);
lean_dec_ref(x_11);
x_234 = x_272;
goto block_237;
}
else
{
lean_object* x_273; 
lean_dec(x_191);
lean_inc_ref(x_11);
lean_inc_ref(x_1);
lean_inc(x_187);
lean_inc_ref(x_193);
x_273 = l_Lake_buildArtifactUnlessUpToDate___lam__1(x_194, x_185, x_193, x_187, x_1, x_6, x_167, x_263, x_7, x_8, x_9, x_10, x_11, x_267);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; 
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; 
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
lean_dec_ref(x_273);
x_276 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_4, x_164, x_167, x_7, x_8, x_9, x_10, x_11, x_275);
lean_dec_ref(x_167);
lean_dec_ref(x_164);
x_234 = x_276;
goto block_237;
}
else
{
lean_object* x_277; lean_object* x_278; 
lean_dec_ref(x_167);
lean_dec_ref(x_164);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_277 = lean_ctor_get(x_273, 1);
lean_inc(x_277);
lean_dec_ref(x_273);
x_278 = lean_ctor_get(x_274, 0);
lean_inc(x_278);
lean_dec_ref(x_274);
x_209 = x_278;
x_210 = x_277;
x_211 = lean_box(0);
goto block_233;
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_187);
lean_dec_ref(x_167);
lean_dec_ref(x_164);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_279 = lean_ctor_get(x_273, 0);
lean_inc(x_279);
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
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(1, 2, 0);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_279);
lean_ctor_set(x_282, 1, x_280);
return x_282;
}
}
}
else
{
lean_inc_ref(x_193);
lean_dec(x_191);
if (x_5 == 0)
{
lean_object* x_283; uint8_t x_284; 
x_283 = lean_ctor_get(x_187, 4);
x_284 = lean_ctor_get_uint8(x_283, sizeof(void*)*26 + 4);
x_238 = x_284;
goto block_262;
}
else
{
x_238 = x_263;
goto block_262;
}
}
block_208:
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec_ref(x_197);
x_205 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_205, 0, x_204);
x_206 = l_Lake_CacheMap_insertCore(x_194, x_205, x_202);
x_207 = lean_st_ref_set(x_200, x_206);
lean_dec(x_200);
x_28 = x_198;
x_29 = x_199;
x_30 = x_196;
x_31 = x_203;
x_32 = lean_box(0);
goto block_36;
}
block_233:
{
lean_object* x_212; 
x_212 = lean_ctor_get(x_187, 21);
lean_inc(x_212);
lean_dec(x_187);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; uint8_t x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_210, 0);
lean_inc_ref(x_213);
x_214 = lean_ctor_get_uint8(x_210, sizeof(void*)*3);
x_215 = lean_ctor_get(x_210, 2);
lean_inc(x_215);
lean_dec_ref(x_210);
x_28 = x_209;
x_29 = x_213;
x_30 = x_214;
x_31 = x_215;
x_32 = lean_box(0);
goto block_36;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; lean_object* x_221; lean_object* x_222; uint64_t x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; 
x_216 = lean_ctor_get(x_212, 0);
lean_inc(x_216);
lean_dec_ref(x_212);
x_217 = lean_st_ref_take(x_216);
x_218 = lean_ctor_get(x_209, 0);
x_219 = lean_ctor_get(x_210, 0);
lean_inc_ref(x_219);
x_220 = lean_ctor_get_uint8(x_210, sizeof(void*)*3);
x_221 = lean_ctor_get(x_210, 1);
lean_inc_ref(x_221);
x_222 = lean_ctor_get(x_210, 2);
lean_inc(x_222);
lean_dec_ref(x_210);
x_223 = lean_ctor_get_uint64(x_218, sizeof(void*)*1);
x_224 = lean_ctor_get(x_218, 0);
x_225 = lean_string_utf8_byte_size(x_224);
x_226 = lean_unsigned_to_nat(0u);
x_227 = lean_nat_dec_eq(x_225, x_226);
lean_dec(x_225);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_228 = l_Lake_Hash_hex(x_223);
x_229 = l_Lake_instToOutputJsonArtifact___lam__0___closed__0;
x_230 = lean_string_append(x_228, x_229);
x_231 = lean_string_append(x_230, x_224);
x_196 = x_220;
x_197 = x_221;
x_198 = x_209;
x_199 = x_219;
x_200 = x_216;
x_201 = lean_box(0);
x_202 = x_217;
x_203 = x_222;
x_204 = x_231;
goto block_208;
}
else
{
lean_object* x_232; 
x_232 = l_Lake_Hash_hex(x_223);
x_196 = x_220;
x_197 = x_221;
x_198 = x_209;
x_199 = x_219;
x_200 = x_216;
x_201 = lean_box(0);
x_202 = x_217;
x_203 = x_222;
x_204 = x_232;
goto block_208;
}
}
}
block_237:
{
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec_ref(x_234);
x_209 = x_235;
x_210 = x_236;
x_211 = lean_box(0);
goto block_233;
}
else
{
lean_dec(x_187);
return x_234;
}
}
block_262:
{
lean_object* x_239; 
lean_inc_ref(x_11);
lean_inc_ref(x_1);
lean_inc(x_187);
lean_inc_ref(x_193);
lean_inc(x_185);
x_239 = l_Lake_buildArtifactUnlessUpToDate___lam__1(x_194, x_185, x_193, x_187, x_1, x_6, x_167, x_238, x_7, x_8, x_9, x_10, x_11, x_192);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; uint8_t x_246; uint8_t x_247; 
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
lean_dec_ref(x_239);
x_242 = l_Lake_SavedTrace_replayIfUpToDate_x27___at___Lake_buildFileUnlessUpToDate_x27_spec__0(x_7, x_1, x_164, x_185, x_195, x_8, x_9, x_10, x_11, x_241);
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec_ref(x_242);
x_245 = 0;
x_246 = lean_unbox(x_243);
x_247 = l_Lake_instDecidableEqOutputStatus(x_246, x_245);
if (x_247 == 0)
{
lean_object* x_248; uint8_t x_249; lean_object* x_250; 
lean_dec_ref(x_167);
lean_dec_ref(x_164);
lean_dec_ref(x_2);
x_248 = lean_box(0);
x_249 = lean_unbox(x_243);
lean_dec(x_243);
lean_inc(x_187);
x_250 = l_Lake_buildArtifactUnlessUpToDate___lam__2(x_249, x_1, x_4, x_3, x_6, x_238, x_187, x_193, x_194, x_248, x_7, x_8, x_9, x_10, x_11, x_244);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_234 = x_250;
goto block_237;
}
else
{
lean_object* x_251; 
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_4);
lean_inc_ref(x_1);
x_251 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_4, x_164, x_167, x_7, x_8, x_9, x_10, x_11, x_244);
lean_dec_ref(x_167);
lean_dec_ref(x_164);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; uint8_t x_254; lean_object* x_255; 
x_252 = lean_ctor_get(x_251, 1);
lean_inc(x_252);
lean_dec_ref(x_251);
x_253 = lean_box(0);
x_254 = lean_unbox(x_243);
lean_dec(x_243);
lean_inc(x_187);
x_255 = l_Lake_buildArtifactUnlessUpToDate___lam__2(x_254, x_1, x_4, x_3, x_6, x_238, x_187, x_193, x_194, x_253, x_7, x_8, x_9, x_10, x_11, x_252);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_234 = x_255;
goto block_237;
}
else
{
lean_dec(x_243);
lean_dec_ref(x_193);
lean_dec(x_187);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_251;
}
}
}
else
{
lean_object* x_256; lean_object* x_257; 
lean_dec_ref(x_193);
lean_dec(x_185);
lean_dec_ref(x_167);
lean_dec_ref(x_164);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_256 = lean_ctor_get(x_239, 1);
lean_inc(x_256);
lean_dec_ref(x_239);
x_257 = lean_ctor_get(x_240, 0);
lean_inc(x_257);
lean_dec_ref(x_240);
x_209 = x_257;
x_210 = x_256;
x_211 = lean_box(0);
goto block_233;
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec_ref(x_193);
lean_dec(x_187);
lean_dec(x_185);
lean_dec_ref(x_167);
lean_dec_ref(x_164);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_258 = lean_ctor_get(x_239, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_239, 1);
lean_inc(x_259);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_260 = x_239;
} else {
 lean_dec_ref(x_239);
 x_260 = lean_box(0);
}
if (lean_is_scalar(x_260)) {
 x_261 = lean_alloc_ctor(1, 2, 0);
} else {
 x_261 = x_260;
}
lean_ctor_set(x_261, 0, x_258);
lean_ctor_set(x_261, 1, x_259);
return x_261;
}
}
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec_ref(x_167);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_285 = lean_ctor_get(x_168, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_168, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_287 = x_168;
} else {
 lean_dec_ref(x_168);
 x_287 = lean_box(0);
}
x_288 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set(x_288, 1, x_164);
lean_ctor_set(x_288, 2, x_165);
lean_ctor_set_uint8(x_288, sizeof(void*)*3, x_163);
if (lean_is_scalar(x_287)) {
 x_289 = lean_alloc_ctor(1, 2, 0);
} else {
 x_289 = x_287;
}
lean_ctor_set(x_289, 0, x_285);
lean_ctor_set(x_289, 1, x_288);
return x_289;
}
}
block_27:
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 1);
lean_dec(x_18);
x_19 = l_Lake_Artifact_trace(x_14);
lean_ctor_set(x_15, 1, x_19);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get_uint8(x_15, sizeof(void*)*3);
x_23 = lean_ctor_get(x_15, 2);
lean_inc(x_23);
lean_inc(x_21);
lean_dec(x_15);
x_24 = l_Lake_Artifact_trace(x_14);
x_25 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*3, x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
block_36:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = l_Lake_Artifact_trace(x_28);
x_34 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_31);
lean_ctor_set_uint8(x_34, sizeof(void*)*3, x_30);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheEnabled___at___Lake_buildArtifactUnlessUpToDate_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Package_isArtifactCacheEnabled___at___Lake_buildArtifactUnlessUpToDate_spec__0___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheEnabled___at___Lake_buildArtifactUnlessUpToDate_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Package_isArtifactCacheEnabled___at___Lake_buildArtifactUnlessUpToDate_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___at___Lake_buildArtifactUnlessUpToDate_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint64_t x_12; lean_object* x_13; 
x_12 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_13 = l_Lake_getArtifacts_x3f___at___Lake_buildArtifactUnlessUpToDate_spec__1(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_buildArtifactUnlessUpToDate___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint64_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_17 = lean_unbox(x_6);
x_18 = lean_unbox(x_8);
x_19 = l_Lake_buildArtifactUnlessUpToDate___lam__1(x_16, x_2, x_3, x_4, x_5, x_17, x_7, x_18, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__2___boxed(lean_object** _args) {
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
uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint64_t x_22; lean_object* x_23; 
x_18 = lean_unbox(x_1);
x_19 = lean_unbox(x_4);
x_20 = lean_unbox(x_5);
x_21 = lean_unbox(x_6);
x_22 = lean_unbox_uint64(x_9);
lean_dec(x_9);
x_23 = l_Lake_buildArtifactUnlessUpToDate___lam__2(x_18, x_2, x_3, x_19, x_20, x_21, x_7, x_8, x_22, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_unbox(x_3);
x_15 = lean_unbox(x_5);
x_16 = lean_unbox(x_6);
x_17 = l_Lake_buildArtifactUnlessUpToDate(x_1, x_2, x_14, x_4, x_15, x_16, x_7, x_8, x_9, x_10, x_11, x_12);
return x_17;
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
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_13 = lean_apply_7(x_1, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_14, 1);
x_18 = l_Lake_BuildTrace_mix(x_17, x_15);
lean_ctor_set(x_14, 1, x_18);
x_19 = lean_apply_1(x_2, x_5);
x_20 = l_Lake_buildFileAfterDep___redArg___lam__0___closed__0;
x_21 = 0;
x_22 = l_Lake_buildArtifactUnlessUpToDate(x_3, x_19, x_4, x_20, x_21, x_21, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_25);
lean_dec(x_24);
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
x_28 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_28);
lean_dec(x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
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
lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_34 = lean_ctor_get(x_14, 0);
x_35 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
x_36 = lean_ctor_get(x_14, 1);
x_37 = lean_ctor_get(x_14, 2);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_34);
lean_dec(x_14);
x_38 = l_Lake_BuildTrace_mix(x_36, x_15);
x_39 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*3, x_35);
x_40 = lean_apply_1(x_2, x_5);
x_41 = l_Lake_buildFileAfterDep___redArg___lam__0___closed__0;
x_42 = 0;
x_43 = l_Lake_buildArtifactUnlessUpToDate(x_3, x_40, x_4, x_41, x_42, x_42, x_6, x_7, x_8, x_9, x_10, x_39);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
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
x_47 = lean_ctor_get(x_44, 1);
lean_inc_ref(x_47);
lean_dec(x_44);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_43, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_43, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_51 = x_43;
} else {
 lean_dec_ref(x_43);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_53 = !lean_is_exclusive(x_13);
if (x_53 == 0)
{
return x_13;
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
return x_56;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_13 = lean_box(x_5);
x_14 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___redArg___lam__0___boxed), 12, 4);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_3);
lean_closure_set(x_14, 2, x_1);
lean_closure_set(x_14, 3, x_13);
x_15 = l_Lake_instDataKindFilePath;
x_16 = lean_unsigned_to_nat(0u);
x_17 = 0;
x_18 = l_Lake_Job_mapM___redArg(x_15, x_2, x_14, x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_14 = lean_box(x_6);
x_15 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___redArg___lam__0___boxed), 12, 4);
lean_closure_set(x_15, 0, x_5);
lean_closure_set(x_15, 1, x_4);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_14);
x_16 = l_Lake_instDataKindFilePath;
x_17 = lean_unsigned_to_nat(0u);
x_18 = 0;
x_19 = l_Lake_Job_mapM___redArg(x_16, x_3, x_15, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
x_14 = l_Lake_buildFileAfterDep___redArg___lam__0(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
x_14 = l_Lake_buildFileAfterDep___redArg(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_6);
x_15 = l_Lake_buildFileAfterDep(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___Lake_inputBinFile_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_computeBinFileHash(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = lean_io_metadata(x_1);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint64_t x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = l_Lake_platformTrace___closed__4;
x_10 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_8);
x_11 = lean_unbox_uint64(x_4);
lean_dec(x_4);
lean_ctor_set_uint64(x_10, sizeof(void*)*3, x_11);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_13);
lean_dec(x_12);
x_14 = l_Lake_platformTrace___closed__4;
x_15 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_13);
x_16 = lean_unbox_uint64(x_4);
lean_dec(x_4);
lean_ctor_set_uint64(x_15, sizeof(void*)*3, x_16);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_4);
lean_dec_ref(x_1);
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
return x_5;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
lean_dec(x_5);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec_ref(x_1);
x_21 = !lean_is_exclusive(x_3);
if (x_21 == 0)
{
return x_3;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_3, 0);
lean_inc(x_22);
lean_dec(x_3);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_get_set_stdout(x_1);
lean_dec_ref(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_get_set_stdout(x_1);
x_16 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
x_17 = lean_box(0);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec_ref(x_16);
lean_inc(x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_18);
x_21 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1___redArg___lam__0(x_15, x_17, x_20, x_19);
lean_dec_ref(x_20);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_18);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_16, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_dec_ref(x_16);
x_28 = lean_box(0);
x_29 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1___redArg___lam__0(x_15, x_17, x_28, x_27);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec_ref(x_29);
x_10 = x_26;
x_11 = x_30;
x_12 = lean_box(0);
goto block_14;
}
block_14:
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_get_set_stdin(x_1);
lean_dec_ref(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_get_set_stdin(x_1);
x_16 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
x_17 = lean_box(0);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec_ref(x_16);
lean_inc(x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_18);
x_21 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2___redArg___lam__0(x_15, x_17, x_20, x_19);
lean_dec_ref(x_20);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_18);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_16, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_dec_ref(x_16);
x_28 = lean_box(0);
x_29 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2___redArg___lam__0(x_15, x_17, x_28, x_27);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec_ref(x_29);
x_10 = x_26;
x_11 = x_30;
x_12 = lean_box(0);
goto block_14;
}
block_14:
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_panic___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_panic___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__3___closed__0;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__4___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_get_set_stderr(x_1);
lean_dec_ref(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_get_set_stderr(x_1);
x_16 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
x_17 = lean_box(0);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec_ref(x_16);
lean_inc(x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_18);
x_21 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__4___redArg___lam__0(x_15, x_17, x_20, x_19);
lean_dec_ref(x_20);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_18);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_16, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_dec_ref(x_16);
x_28 = lean_box(0);
x_29 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__4___redArg___lam__0(x_15, x_17, x_28, x_27);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec_ref(x_29);
x_10 = x_26;
x_11 = x_30;
x_12 = lean_box(0);
goto block_14;
}
block_14:
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__4___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_1 = lean_mk_string_unchecked("Init.Data.String.Basic", 22, 22);
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
x_2 = lean_unsigned_to_nat(46u);
x_3 = lean_unsigned_to_nat(244u);
x_4 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__2;
x_5 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__1;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__0;
x_18 = lean_st_mk_ref(x_17);
x_19 = lean_st_mk_ref(x_17);
x_20 = l_IO_FS_Stream_ofBuffer(x_18);
lean_inc(x_19);
x_21 = l_IO_FS_Stream_ofBuffer(x_19);
if (x_2 == 0)
{
x_22 = x_1;
goto block_37;
}
else
{
lean_object* x_38; 
lean_inc_ref(x_21);
x_38 = lean_alloc_closure((void*)(l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__4___boxed), 10, 3);
lean_closure_set(x_38, 0, lean_box(0));
lean_closure_set(x_38, 1, x_21);
lean_closure_set(x_38, 2, x_1);
x_22 = x_38;
goto block_37;
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
block_37:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_alloc_closure((void*)(l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1___boxed), 10, 3);
lean_closure_set(x_23, 0, lean_box(0));
lean_closure_set(x_23, 1, x_21);
lean_closure_set(x_23, 2, x_22);
x_24 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2___redArg(x_20, x_23, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = lean_st_ref_get(x_19);
lean_dec(x_19);
x_28 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_28);
lean_dec_ref(x_27);
lean_inc_ref(x_28);
x_29 = lean_string_validate_utf8(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec_ref(x_28);
x_30 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__4;
x_31 = l_panic___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__3(x_30);
x_10 = x_25;
x_11 = lean_box(0);
x_12 = x_26;
x_13 = x_31;
goto block_16;
}
else
{
lean_object* x_32; 
x_32 = lean_string_from_utf8_unchecked(x_28);
x_10 = x_25;
x_11 = lean_box(0);
x_12 = x_26;
x_13 = x_32;
goto block_16;
}
}
else
{
uint8_t x_33; 
lean_dec(x_19);
x_33 = !lean_is_exclusive(x_24);
if (x_33 == 0)
{
return x_24;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_24, 0);
x_35 = lean_ctor_get(x_24, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_24);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_inputBinFile_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_inputBinFile_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_1);
x_12 = l_Lake_BuildTrace_compute___at___Lake_inputBinFile_spec__0(x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
lean_ctor_set(x_7, 1, x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_1);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec_ref(x_12);
x_16 = lean_io_error_to_string(x_15);
x_17 = 3;
x_18 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_17);
x_19 = lean_array_get_size(x_10);
x_20 = lean_array_push(x_10, x_18);
lean_ctor_set(x_7, 0, x_20);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_7);
return x_21;
}
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get_uint8(x_7, sizeof(void*)*3);
x_24 = lean_ctor_get(x_7, 1);
x_25 = lean_ctor_get(x_7, 2);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_22);
lean_dec(x_7);
lean_inc_ref(x_1);
x_26 = l_Lake_BuildTrace_compute___at___Lake_inputBinFile_spec__0(x_1);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec_ref(x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_23);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec_ref(x_1);
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
lean_dec_ref(x_26);
x_31 = lean_io_error_to_string(x_30);
x_32 = 3;
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
x_34 = lean_array_get_size(x_22);
x_35 = lean_array_push(x_22, x_33);
x_36 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_24);
lean_ctor_set(x_36, 2, x_25);
lean_ctor_set_uint8(x_36, sizeof(void*)*3, x_23);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
return x_37;
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
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_21; uint8_t x_22; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_14 = x_11;
} else {
 lean_dec_ref(x_11);
 x_14 = lean_box(0);
}
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_21 = lean_string_utf8_byte_size(x_15);
x_22 = lean_nat_dec_eq(x_21, x_9);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_26 = l_Substring_takeWhileAux___at___Lake_inputBinFile_spec__6(x_15, x_21, x_9);
x_27 = l_Substring_takeRightWhileAux___at___Lake_inputBinFile_spec__7(x_15, x_26, x_21);
x_28 = lean_string_utf8_extract(x_15, x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_15);
x_29 = lean_string_append(x_25, x_28);
lean_dec_ref(x_28);
x_30 = 1;
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_30);
x_32 = lean_array_push(x_24, x_31);
lean_ctor_set(x_13, 0, x_32);
x_17 = x_13;
x_18 = lean_box(0);
goto block_20;
}
else
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_ctor_get_uint8(x_13, sizeof(void*)*3);
x_35 = lean_ctor_get(x_13, 1);
x_36 = lean_ctor_get(x_13, 2);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_33);
lean_dec(x_13);
x_37 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_38 = l_Substring_takeWhileAux___at___Lake_inputBinFile_spec__6(x_15, x_21, x_9);
x_39 = l_Substring_takeRightWhileAux___at___Lake_inputBinFile_spec__7(x_15, x_38, x_21);
x_40 = lean_string_utf8_extract(x_15, x_38, x_39);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_15);
x_41 = lean_string_append(x_37, x_40);
lean_dec_ref(x_40);
x_42 = 1;
x_43 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_42);
x_44 = lean_array_push(x_33, x_43);
x_45 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_35);
lean_ctor_set(x_45, 2, x_36);
lean_ctor_set_uint8(x_45, sizeof(void*)*3, x_34);
x_17 = x_45;
x_18 = lean_box(0);
goto block_20;
}
}
else
{
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_9);
x_17 = x_13;
x_18 = lean_box(0);
goto block_20;
}
block_20:
{
lean_object* x_19; 
if (lean_is_scalar(x_14)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_14;
}
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_46; 
lean_dec(x_9);
x_46 = !lean_is_exclusive(x_11);
if (x_46 == 0)
{
return x_11;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_11, 0);
x_48 = lean_ctor_get(x_11, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_11);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
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
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lake_inputBinFile___redArg___closed__1;
x_3 = 0;
x_4 = l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_8 = lean_alloc_closure((void*)(l_Lake_inputBinFile___redArg___lam__0___boxed), 8, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = 1;
x_11 = l_Lake_inputBinFile___redArg___closed__2;
x_12 = lean_box(x_10);
x_13 = lean_alloc_closure((void*)(l_Lake_inputBinFile___redArg___lam__1___boxed), 10, 9);
lean_closure_set(x_13, 0, x_8);
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_4);
lean_closure_set(x_13, 5, x_5);
lean_closure_set(x_13, 6, x_6);
lean_closure_set(x_13, 7, x_11);
lean_closure_set(x_13, 8, x_9);
x_14 = lean_io_as_task(x_13, x_9);
x_15 = l_Lake_instDataKindFilePath;
x_16 = l_panic___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__3___closed__0;
x_17 = 0;
x_18 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_inputBinFile___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___Lake_inputBinFile_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_BuildTrace_compute___at___Lake_inputBinFile_spec__0(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__4___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__4___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
x_12 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_inputBinFile_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeWhileAux___at___Lake_inputBinFile_spec__6(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_inputBinFile_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeRightWhileAux___at___Lake_inputBinFile_spec__7(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_inputBinFile___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
x_12 = l_Lake_inputBinFile___redArg___lam__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_inputBinFile___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_inputBinFile(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___Lake_inputTextFile_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_computeTextFileHash(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = lean_io_metadata(x_1);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint64_t x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = l_Lake_platformTrace___closed__4;
x_10 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_8);
x_11 = lean_unbox_uint64(x_4);
lean_dec(x_4);
lean_ctor_set_uint64(x_10, sizeof(void*)*3, x_11);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_13);
lean_dec(x_12);
x_14 = l_Lake_platformTrace___closed__4;
x_15 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_13);
x_16 = lean_unbox_uint64(x_4);
lean_dec(x_4);
lean_ctor_set_uint64(x_15, sizeof(void*)*3, x_16);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_4);
lean_dec_ref(x_1);
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
return x_5;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
lean_dec(x_5);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec_ref(x_1);
x_21 = !lean_is_exclusive(x_3);
if (x_21 == 0)
{
return x_3;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_3, 0);
lean_inc(x_22);
lean_dec(x_3);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_1);
x_12 = l_Lake_BuildTrace_compute___at___Lake_inputTextFile_spec__0(x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
lean_ctor_set(x_7, 1, x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_1);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec_ref(x_12);
x_16 = lean_io_error_to_string(x_15);
x_17 = 3;
x_18 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_17);
x_19 = lean_array_get_size(x_10);
x_20 = lean_array_push(x_10, x_18);
lean_ctor_set(x_7, 0, x_20);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_7);
return x_21;
}
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get_uint8(x_7, sizeof(void*)*3);
x_24 = lean_ctor_get(x_7, 1);
x_25 = lean_ctor_get(x_7, 2);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_22);
lean_dec(x_7);
lean_inc_ref(x_1);
x_26 = l_Lake_BuildTrace_compute___at___Lake_inputTextFile_spec__0(x_1);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec_ref(x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_23);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec_ref(x_1);
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
lean_dec_ref(x_26);
x_31 = lean_io_error_to_string(x_30);
x_32 = 3;
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
x_34 = lean_array_get_size(x_22);
x_35 = lean_array_push(x_22, x_33);
x_36 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_24);
lean_ctor_set(x_36, 2, x_25);
lean_ctor_set_uint8(x_36, sizeof(void*)*3, x_23);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_21; uint8_t x_22; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_14 = x_11;
} else {
 lean_dec_ref(x_11);
 x_14 = lean_box(0);
}
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_21 = lean_string_utf8_byte_size(x_15);
x_22 = lean_nat_dec_eq(x_21, x_9);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_26 = l_Substring_takeWhileAux___at___Lake_inputBinFile_spec__6(x_15, x_21, x_9);
x_27 = l_Substring_takeRightWhileAux___at___Lake_inputBinFile_spec__7(x_15, x_26, x_21);
x_28 = lean_string_utf8_extract(x_15, x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_15);
x_29 = lean_string_append(x_25, x_28);
lean_dec_ref(x_28);
x_30 = 1;
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_30);
x_32 = lean_array_push(x_24, x_31);
lean_ctor_set(x_13, 0, x_32);
x_17 = x_13;
x_18 = lean_box(0);
goto block_20;
}
else
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_ctor_get_uint8(x_13, sizeof(void*)*3);
x_35 = lean_ctor_get(x_13, 1);
x_36 = lean_ctor_get(x_13, 2);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_33);
lean_dec(x_13);
x_37 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_38 = l_Substring_takeWhileAux___at___Lake_inputBinFile_spec__6(x_15, x_21, x_9);
x_39 = l_Substring_takeRightWhileAux___at___Lake_inputBinFile_spec__7(x_15, x_38, x_21);
x_40 = lean_string_utf8_extract(x_15, x_38, x_39);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_15);
x_41 = lean_string_append(x_37, x_40);
lean_dec_ref(x_40);
x_42 = 1;
x_43 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_42);
x_44 = lean_array_push(x_33, x_43);
x_45 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_35);
lean_ctor_set(x_45, 2, x_36);
lean_ctor_set_uint8(x_45, sizeof(void*)*3, x_34);
x_17 = x_45;
x_18 = lean_box(0);
goto block_20;
}
}
else
{
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_9);
x_17 = x_13;
x_18 = lean_box(0);
goto block_20;
}
block_20:
{
lean_object* x_19; 
if (lean_is_scalar(x_14)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_14;
}
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_46; 
lean_dec(x_9);
x_46 = !lean_is_exclusive(x_11);
if (x_46 == 0)
{
return x_11;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_11, 0);
x_48 = lean_ctor_get(x_11, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_11);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_8 = lean_alloc_closure((void*)(l_Lake_inputTextFile___redArg___lam__0___boxed), 8, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = 1;
x_11 = l_Lake_inputBinFile___redArg___closed__2;
x_12 = lean_box(x_10);
x_13 = lean_alloc_closure((void*)(l_Lake_inputTextFile___redArg___lam__1___boxed), 10, 9);
lean_closure_set(x_13, 0, x_8);
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_4);
lean_closure_set(x_13, 5, x_5);
lean_closure_set(x_13, 6, x_6);
lean_closure_set(x_13, 7, x_11);
lean_closure_set(x_13, 8, x_9);
x_14 = lean_io_as_task(x_13, x_9);
x_15 = l_Lake_instDataKindFilePath;
x_16 = l_panic___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__3___closed__0;
x_17 = 0;
x_18 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_inputTextFile___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___Lake_inputTextFile_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_BuildTrace_compute___at___Lake_inputTextFile_spec__0(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_inputTextFile___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
x_12 = l_Lake_inputTextFile___redArg___lam__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_inputTextFile___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_inputTextFile(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (x_2 == 0)
{
lean_object* x_9; 
x_9 = l_Lake_inputBinFile___redArg(x_1, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = l_Lake_inputTextFile___redArg(x_1, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (x_2 == 0)
{
lean_object* x_10; 
x_10 = l_Lake_inputBinFile___redArg(x_1, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = l_Lake_inputTextFile___redArg(x_1, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lake_inputFile___redArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_Lake_inputFile(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_8);
return x_11;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_dec_lt(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_5 = lean_alloc_closure((void*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__0___redArg___lam__0___boxed), 2, 0);
lean_inc(x_2);
x_6 = l_Array_qpartition___redArg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__0___redArg(x_8, x_2, x_7);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__0___redArg(x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_inputDir_spec__1___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_15; 
x_15 = lean_usize_dec_eq(x_3, x_4);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_uget(x_2, x_3);
x_17 = l_System_FilePath_isDir(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
lean_inc_ref(x_1);
lean_inc_ref(x_16);
x_18 = lean_apply_1(x_1, x_16);
x_19 = lean_unbox(x_18);
if (x_19 == 0)
{
lean_dec_ref(x_16);
x_8 = x_5;
x_9 = x_6;
x_10 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_20; 
x_20 = lean_array_push(x_5, x_16);
x_8 = x_20;
x_9 = x_6;
x_10 = lean_box(0);
goto block_14;
}
}
else
{
lean_dec_ref(x_16);
x_8 = x_5;
x_9 = x_6;
x_10 = lean_box(0);
goto block_14;
}
}
else
{
lean_object* x_21; 
lean_dec_ref(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_6);
return x_21;
}
block_14:
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
x_5 = x_8;
x_6 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_inputDir_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_inputDir_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_inputDir_spec__2(uint8_t x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_array_uget(x_4, x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_4, x_3, x_15);
if (x_1 == 0)
{
lean_object* x_23; 
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_23 = l_Lake_inputBinFile___redArg(x_14, x_5, x_6, x_7, x_8, x_9);
x_17 = x_23;
goto block_22;
}
else
{
lean_object* x_24; 
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_24 = l_Lake_inputTextFile___redArg(x_14, x_5, x_6, x_7, x_8, x_9);
x_17 = x_24;
goto block_22;
}
block_22:
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_20 = lean_array_uset(x_16, x_3, x_17);
x_3 = x_19;
x_4 = x_20;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__3___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__3___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__3___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_17; 
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_9, 0);
lean_inc(x_26);
lean_dec_ref(x_9);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_25, 1);
x_29 = l_Lake_BuildTrace_mix(x_1, x_28);
x_30 = lean_apply_1(x_2, x_26);
x_31 = 1;
lean_ctor_set(x_25, 1, x_29);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_32 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_30, x_31, x_3, x_4, x_5, x_6, x_7, x_25);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_string_utf8_byte_size(x_35);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_nat_dec_eq(x_37, x_38);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_34);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_41 = lean_ctor_get(x_34, 0);
x_42 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_43 = l_Substring_takeWhileAux___at___Lake_inputBinFile_spec__6(x_35, x_37, x_38);
x_44 = l_Substring_takeRightWhileAux___at___Lake_inputBinFile_spec__7(x_35, x_43, x_37);
x_45 = lean_string_utf8_extract(x_35, x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_35);
x_46 = lean_string_append(x_42, x_45);
lean_dec_ref(x_45);
x_47 = 1;
x_48 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_47);
x_49 = lean_box(0);
x_50 = lean_array_push(x_41, x_48);
lean_ctor_set(x_34, 0, x_50);
x_51 = l_Lake_Job_bindM___at___Lake_inputDir_spec__3___redArg___lam__1(x_36, x_49, x_3, x_4, x_5, x_6, x_7, x_34);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_17 = x_51;
goto block_24;
}
else
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_52 = lean_ctor_get(x_34, 0);
x_53 = lean_ctor_get_uint8(x_34, sizeof(void*)*3);
x_54 = lean_ctor_get(x_34, 1);
x_55 = lean_ctor_get(x_34, 2);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_52);
lean_dec(x_34);
x_56 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_57 = l_Substring_takeWhileAux___at___Lake_inputBinFile_spec__6(x_35, x_37, x_38);
x_58 = l_Substring_takeRightWhileAux___at___Lake_inputBinFile_spec__7(x_35, x_57, x_37);
x_59 = lean_string_utf8_extract(x_35, x_57, x_58);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_35);
x_60 = lean_string_append(x_56, x_59);
lean_dec_ref(x_59);
x_61 = 1;
x_62 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_61);
x_63 = lean_box(0);
x_64 = lean_array_push(x_52, x_62);
x_65 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_54);
lean_ctor_set(x_65, 2, x_55);
lean_ctor_set_uint8(x_65, sizeof(void*)*3, x_53);
x_66 = l_Lake_Job_bindM___at___Lake_inputDir_spec__3___redArg___lam__1(x_36, x_63, x_3, x_4, x_5, x_6, x_7, x_65);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_17 = x_66;
goto block_24;
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_37);
lean_dec(x_35);
x_67 = lean_box(0);
x_68 = l_Lake_Job_bindM___at___Lake_inputDir_spec__3___redArg___lam__1(x_36, x_67, x_3, x_4, x_5, x_6, x_7, x_34);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_17 = x_68;
goto block_24;
}
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_69 = lean_ctor_get(x_32, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_32, 1);
lean_inc(x_70);
lean_dec_ref(x_32);
x_11 = x_69;
x_12 = x_70;
x_13 = lean_box(0);
goto block_16;
}
}
else
{
lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; 
x_71 = lean_ctor_get(x_25, 0);
x_72 = lean_ctor_get_uint8(x_25, sizeof(void*)*3);
x_73 = lean_ctor_get(x_25, 1);
x_74 = lean_ctor_get(x_25, 2);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_71);
lean_dec(x_25);
x_75 = l_Lake_BuildTrace_mix(x_1, x_73);
x_76 = lean_apply_1(x_2, x_26);
x_77 = 1;
x_78 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_78, 0, x_71);
lean_ctor_set(x_78, 1, x_75);
lean_ctor_set(x_78, 2, x_74);
lean_ctor_set_uint8(x_78, sizeof(void*)*3, x_72);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_79 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_76, x_77, x_3, x_4, x_5, x_6, x_7, x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec_ref(x_79);
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_84 = lean_string_utf8_byte_size(x_82);
x_85 = lean_unsigned_to_nat(0u);
x_86 = lean_nat_dec_eq(x_84, x_85);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_87 = lean_ctor_get(x_81, 0);
lean_inc_ref(x_87);
x_88 = lean_ctor_get_uint8(x_81, sizeof(void*)*3);
x_89 = lean_ctor_get(x_81, 1);
lean_inc_ref(x_89);
x_90 = lean_ctor_get(x_81, 2);
lean_inc(x_90);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 lean_ctor_release(x_81, 2);
 x_91 = x_81;
} else {
 lean_dec_ref(x_81);
 x_91 = lean_box(0);
}
x_92 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_93 = l_Substring_takeWhileAux___at___Lake_inputBinFile_spec__6(x_82, x_84, x_85);
x_94 = l_Substring_takeRightWhileAux___at___Lake_inputBinFile_spec__7(x_82, x_93, x_84);
x_95 = lean_string_utf8_extract(x_82, x_93, x_94);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_82);
x_96 = lean_string_append(x_92, x_95);
lean_dec_ref(x_95);
x_97 = 1;
x_98 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set_uint8(x_98, sizeof(void*)*1, x_97);
x_99 = lean_box(0);
x_100 = lean_array_push(x_87, x_98);
if (lean_is_scalar(x_91)) {
 x_101 = lean_alloc_ctor(0, 3, 1);
} else {
 x_101 = x_91;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_89);
lean_ctor_set(x_101, 2, x_90);
lean_ctor_set_uint8(x_101, sizeof(void*)*3, x_88);
x_102 = l_Lake_Job_bindM___at___Lake_inputDir_spec__3___redArg___lam__1(x_83, x_99, x_3, x_4, x_5, x_6, x_7, x_101);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_17 = x_102;
goto block_24;
}
else
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_84);
lean_dec(x_82);
x_103 = lean_box(0);
x_104 = l_Lake_Job_bindM___at___Lake_inputDir_spec__3___redArg___lam__1(x_83, x_103, x_3, x_4, x_5, x_6, x_7, x_81);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_17 = x_104;
goto block_24;
}
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_105 = lean_ctor_get(x_79, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_79, 1);
lean_inc(x_106);
lean_dec_ref(x_79);
x_11 = x_105;
x_12 = x_106;
x_13 = lean_box(0);
goto block_16;
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_107 = !lean_is_exclusive(x_9);
if (x_107 == 0)
{
lean_object* x_108; 
x_108 = lean_task_pure(x_9);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_9, 0);
x_110 = lean_ctor_get(x_9, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_9);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_task_pure(x_111);
return x_112;
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_task_pure(x_14);
return x_15;
}
block_24:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_20);
lean_dec(x_18);
x_21 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_inputDir_spec__3___redArg___lam__0), 2, 1);
lean_closure_set(x_21, 0, x_19);
x_22 = 1;
x_23 = lean_task_map(x_21, x_20, x_8, x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_dec(x_14);
lean_inc(x_3);
x_15 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_inputDir_spec__3___redArg___lam__2___boxed), 10, 8);
lean_closure_set(x_15, 0, x_10);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_5);
lean_closure_set(x_15, 3, x_6);
lean_closure_set(x_15, 4, x_7);
lean_closure_set(x_15, 5, x_8);
lean_closure_set(x_15, 6, x_9);
lean_closure_set(x_15, 7, x_3);
x_16 = lean_io_bind_task(x_13, x_15, x_3, x_4);
x_17 = lean_box(0);
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_16);
return x_1;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 2);
x_20 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
lean_inc(x_3);
x_21 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_inputDir_spec__3___redArg___lam__2___boxed), 10, 8);
lean_closure_set(x_21, 0, x_10);
lean_closure_set(x_21, 1, x_2);
lean_closure_set(x_21, 2, x_5);
lean_closure_set(x_21, 3, x_6);
lean_closure_set(x_21, 4, x_7);
lean_closure_set(x_21, 5, x_8);
lean_closure_set(x_21, 6, x_9);
lean_closure_set(x_21, 7, x_3);
x_22 = lean_io_bind_task(x_18, x_21, x_3, x_4);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_20);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_Job_bindM___at___Lake_inputDir_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_inputDir___lam__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_9, 0);
x_33 = lean_ctor_get_uint8(x_9, sizeof(void*)*3);
x_34 = lean_ctor_get(x_9, 1);
x_35 = lean_ctor_get(x_9, 2);
x_36 = l_System_FilePath_walkDir(x_1, x_2);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = lean_unsigned_to_nat(0u);
x_48 = lean_array_get_size(x_37);
x_49 = l_Lake_inputDir___lam__1___closed__0;
x_50 = lean_nat_dec_lt(x_38, x_48);
if (x_50 == 0)
{
lean_dec(x_48);
lean_dec(x_37);
lean_dec_ref(x_3);
x_39 = x_49;
x_40 = x_9;
x_41 = lean_box(0);
goto block_47;
}
else
{
uint8_t x_51; 
x_51 = lean_nat_dec_le(x_48, x_48);
if (x_51 == 0)
{
lean_dec(x_48);
lean_dec(x_37);
lean_dec_ref(x_3);
x_39 = x_49;
x_40 = x_9;
x_41 = lean_box(0);
goto block_47;
}
else
{
size_t x_52; size_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = 0;
x_53 = lean_usize_of_nat(x_48);
lean_dec(x_48);
x_54 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_inputDir_spec__1___redArg(x_3, x_37, x_52, x_53, x_49, x_9);
lean_dec(x_37);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec_ref(x_54);
x_39 = x_55;
x_40 = x_56;
x_41 = lean_box(0);
goto block_47;
}
}
block_47:
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_array_get_size(x_39);
x_43 = lean_nat_dec_eq(x_42, x_38);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_sub(x_42, x_44);
x_46 = lean_nat_dec_le(x_38, x_45);
if (x_46 == 0)
{
lean_inc(x_45);
x_24 = x_42;
x_25 = x_40;
x_26 = lean_box(0);
x_27 = x_45;
x_28 = x_39;
x_29 = x_45;
goto block_31;
}
else
{
x_24 = x_42;
x_25 = x_40;
x_26 = lean_box(0);
x_27 = x_45;
x_28 = x_39;
x_29 = x_38;
goto block_31;
}
}
else
{
lean_dec(x_42);
x_11 = x_40;
x_12 = lean_box(0);
x_13 = x_39;
goto block_15;
}
}
}
else
{
uint8_t x_57; 
lean_inc(x_35);
lean_inc_ref(x_34);
lean_inc_ref(x_32);
lean_dec_ref(x_3);
x_57 = !lean_is_exclusive(x_9);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_58 = lean_ctor_get(x_9, 2);
lean_dec(x_58);
x_59 = lean_ctor_get(x_9, 1);
lean_dec(x_59);
x_60 = lean_ctor_get(x_9, 0);
lean_dec(x_60);
x_61 = lean_ctor_get(x_36, 0);
lean_inc(x_61);
lean_dec_ref(x_36);
x_62 = lean_io_error_to_string(x_61);
x_63 = 3;
x_64 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_63);
x_65 = lean_array_get_size(x_32);
x_66 = lean_array_push(x_32, x_64);
lean_ctor_set(x_9, 0, x_66);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_9);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_9);
x_68 = lean_ctor_get(x_36, 0);
lean_inc(x_68);
lean_dec_ref(x_36);
x_69 = lean_io_error_to_string(x_68);
x_70 = 3;
x_71 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_70);
x_72 = lean_array_get_size(x_32);
x_73 = lean_array_push(x_32, x_71);
x_74 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_34);
lean_ctor_set(x_74, 2, x_35);
lean_ctor_set_uint8(x_74, sizeof(void*)*3, x_33);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
block_15:
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
block_23:
{
lean_object* x_22; 
lean_dec(x_16);
x_22 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__0___redArg(x_20, x_19, x_21);
lean_dec(x_21);
x_11 = x_17;
x_12 = lean_box(0);
x_13 = x_22;
goto block_15;
}
block_31:
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_29, x_27);
if (x_30 == 0)
{
lean_dec(x_27);
lean_inc(x_29);
x_16 = x_24;
x_17 = x_25;
x_18 = lean_box(0);
x_19 = x_29;
x_20 = x_28;
x_21 = x_29;
goto block_23;
}
else
{
x_16 = x_24;
x_17 = x_25;
x_18 = lean_box(0);
x_19 = x_29;
x_20 = x_28;
x_21 = x_27;
goto block_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_21; uint8_t x_22; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_14 = x_11;
} else {
 lean_dec_ref(x_11);
 x_14 = lean_box(0);
}
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_21 = lean_string_utf8_byte_size(x_15);
x_22 = lean_nat_dec_eq(x_21, x_9);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_26 = l_Substring_takeWhileAux___at___Lake_inputBinFile_spec__6(x_15, x_21, x_9);
x_27 = l_Substring_takeRightWhileAux___at___Lake_inputBinFile_spec__7(x_15, x_26, x_21);
x_28 = lean_string_utf8_extract(x_15, x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_15);
x_29 = lean_string_append(x_25, x_28);
lean_dec_ref(x_28);
x_30 = 1;
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_30);
x_32 = lean_array_push(x_24, x_31);
lean_ctor_set(x_13, 0, x_32);
x_17 = x_13;
x_18 = lean_box(0);
goto block_20;
}
else
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_ctor_get_uint8(x_13, sizeof(void*)*3);
x_35 = lean_ctor_get(x_13, 1);
x_36 = lean_ctor_get(x_13, 2);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_33);
lean_dec(x_13);
x_37 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_38 = l_Substring_takeWhileAux___at___Lake_inputBinFile_spec__6(x_15, x_21, x_9);
x_39 = l_Substring_takeRightWhileAux___at___Lake_inputBinFile_spec__7(x_15, x_38, x_21);
x_40 = lean_string_utf8_extract(x_15, x_38, x_39);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_15);
x_41 = lean_string_append(x_37, x_40);
lean_dec_ref(x_40);
x_42 = 1;
x_43 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_42);
x_44 = lean_array_push(x_33, x_43);
x_45 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_35);
lean_ctor_set(x_45, 2, x_36);
lean_ctor_set_uint8(x_45, sizeof(void*)*3, x_34);
x_17 = x_45;
x_18 = lean_box(0);
goto block_20;
}
}
else
{
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_9);
x_17 = x_13;
x_18 = lean_box(0);
goto block_20;
}
block_20:
{
lean_object* x_19; 
if (lean_is_scalar(x_14)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_14;
}
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_46; 
lean_dec(x_9);
x_46 = !lean_is_exclusive(x_11);
if (x_46 == 0)
{
return x_11;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_11, 0);
x_48 = lean_ctor_get(x_11, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_11);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_array_size(x_3);
x_12 = 0;
x_13 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_inputDir_spec__2(x_1, x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lake_Job_collectArray___redArg(x_15, x_2);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = l_Lake_Job_collectArray___redArg(x_17, x_2);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_11 = lean_alloc_closure((void*)(l_Lake_inputDir___lam__0___boxed), 2, 0);
lean_inc_ref(x_1);
x_12 = lean_alloc_closure((void*)(l_Lake_inputDir___lam__1___boxed), 10, 3);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
lean_closure_set(x_12, 2, x_3);
x_13 = lean_unsigned_to_nat(0u);
x_14 = 1;
x_15 = l_Lake_inputBinFile___redArg___closed__2;
x_16 = lean_box(x_14);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_17 = lean_alloc_closure((void*)(l_Lake_inputDir___lam__2___boxed), 10, 9);
lean_closure_set(x_17, 0, x_12);
lean_closure_set(x_17, 1, x_16);
lean_closure_set(x_17, 2, x_4);
lean_closure_set(x_17, 3, x_5);
lean_closure_set(x_17, 4, x_6);
lean_closure_set(x_17, 5, x_7);
lean_closure_set(x_17, 6, x_8);
lean_closure_set(x_17, 7, x_15);
lean_closure_set(x_17, 8, x_13);
x_18 = lean_io_as_task(x_17, x_13);
x_19 = lean_box(x_2);
x_20 = lean_alloc_closure((void*)(l_Lake_inputDir___lam__3___boxed), 10, 2);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_1);
x_21 = lean_box(0);
x_22 = l_panic___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__3___closed__0;
x_23 = 0;
x_24 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_23);
x_25 = l_Lake_Job_bindM___at___Lake_inputDir_spec__3___redArg(x_24, x_20, x_13, x_23, x_4, x_5, x_6, x_7, x_8, x_9);
return x_25;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__0___redArg___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_inputDir_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_inputDir_spec__1___redArg(x_1, x_2, x_8, x_9, x_5, x_6);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_inputDir_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_inputDir_spec__1(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_inputDir_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_inputDir_spec__2(x_12, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__3___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_Job_bindM___at___Lake_inputDir_spec__3___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__3___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_Job_bindM___at___Lake_inputDir_spec__3___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
x_13 = l_Lake_Job_bindM___at___Lake_inputDir_spec__3___redArg(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
x_14 = l_Lake_Job_bindM___at___Lake_inputDir_spec__3(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_inputDir___lam__0(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_inputDir___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
x_12 = l_Lake_inputDir___lam__2(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
x_12 = l_Lake_inputDir___lam__3(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
x_12 = l_Lake_inputDir(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT uint64_t l_Lake_buildO___lam__0(uint64_t x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; 
x_3 = l_Lake_platformTrace___closed__1;
x_4 = lean_string_hash(x_2);
x_5 = lean_uint64_mix_hash(x_3, x_4);
x_6 = lean_uint64_mix_hash(x_1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = l_Lake_compileO(x_1, x_2, x_3, x_4, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 1);
lean_ctor_set(x_10, 0, x_16);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_14);
lean_ctor_set(x_10, 0, x_18);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_10);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_14, 1);
lean_ctor_set(x_10, 0, x_21);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
lean_ctor_set(x_10, 0, x_23);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_10);
return x_24;
}
}
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
x_27 = lean_ctor_get(x_10, 1);
x_28 = lean_ctor_get(x_10, 2);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_25);
lean_dec(x_10);
x_29 = l_Lake_compileO(x_1, x_2, x_3, x_4, x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
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
x_33 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_27);
lean_ctor_set(x_33, 2, x_28);
lean_ctor_set_uint8(x_33, sizeof(void*)*3, x_26);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_37 = x_29;
} else {
 lean_dec_ref(x_29);
 x_37 = lean_box(0);
}
x_38 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_27);
lean_ctor_set(x_38, 2, x_28);
lean_ctor_set_uint8(x_38, sizeof(void*)*3, x_26);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_38);
return x_39;
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
x_1 = l_Lake_platformTrace___closed__1;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; uint64_t x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_17);
x_18 = lean_ctor_get_uint8(x_15, sizeof(void*)*3);
x_19 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_15, 2);
lean_inc(x_20);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 x_21 = x_15;
} else {
 lean_dec_ref(x_15);
 x_21 = lean_box(0);
}
x_22 = l_Lake_platformTrace;
x_23 = l_Lake_BuildTrace_mix(x_19, x_22);
x_83 = l_Lake_platformTrace___closed__1;
x_84 = lean_unsigned_to_nat(0u);
x_85 = lean_array_get_size(x_1);
x_86 = lean_nat_dec_lt(x_84, x_85);
if (x_86 == 0)
{
lean_dec(x_85);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_24 = x_83;
goto block_82;
}
else
{
uint8_t x_87; 
x_87 = lean_nat_dec_le(x_85, x_85);
if (x_87 == 0)
{
lean_dec(x_85);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_24 = x_83;
goto block_82;
}
else
{
size_t x_88; size_t x_89; lean_object* x_90; lean_object* x_91; uint64_t x_92; 
x_88 = 0;
x_89 = lean_usize_of_nat(x_85);
lean_dec(x_85);
x_90 = l_Lake_buildO___lam__2___boxed__const__1;
lean_inc_ref(x_1);
x_91 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_7, x_8, x_1, x_88, x_89, x_90);
x_92 = lean_unbox_uint64(x_91);
lean_dec(x_91);
x_24 = x_92;
goto block_82;
}
}
block_82:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_25 = l_Lake_buildO___lam__2___closed__0;
x_26 = l_Lake_buildO___lam__2___closed__1;
lean_inc_ref(x_1);
x_27 = lean_array_to_list(x_1);
x_28 = l_List_toString___redArg(x_2, x_27);
x_29 = lean_string_append(x_26, x_28);
lean_dec_ref(x_28);
x_30 = lean_string_append(x_25, x_29);
lean_dec_ref(x_29);
x_31 = l_Lake_platformTrace___closed__4;
x_32 = l_Lake_platformTrace___closed__6;
x_33 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set_uint64(x_33, sizeof(void*)*3, x_24);
x_34 = l_Lake_BuildTrace_mix(x_23, x_33);
if (lean_is_scalar(x_21)) {
 x_35 = lean_alloc_ctor(0, 3, 1);
} else {
 x_35 = x_21;
}
lean_ctor_set(x_35, 0, x_17);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_20);
lean_ctor_set_uint8(x_35, sizeof(void*)*3, x_18);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_36 = lean_apply_7(x_3, x_10, x_11, x_12, x_13, x_14, x_35, lean_box(0));
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec_ref(x_36);
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_37, 1);
x_41 = l_Lake_BuildTrace_mix(x_40, x_38);
lean_ctor_set(x_37, 1, x_41);
x_42 = l_Array_append___redArg(x_4, x_1);
lean_dec_ref(x_1);
lean_inc_ref(x_5);
x_43 = lean_alloc_closure((void*)(l_Lake_buildO___lam__1___boxed), 11, 4);
lean_closure_set(x_43, 0, x_5);
lean_closure_set(x_43, 1, x_9);
lean_closure_set(x_43, 2, x_42);
lean_closure_set(x_43, 3, x_6);
x_44 = 0;
x_45 = l_Lake_buildO___lam__2___closed__2;
x_46 = l_Lake_buildArtifactUnlessUpToDate(x_5, x_43, x_44, x_45, x_44, x_44, x_10, x_11, x_12, x_13, x_14, x_37);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ctor_get(x_48, 1);
lean_inc_ref(x_49);
lean_dec(x_48);
lean_ctor_set(x_46, 0, x_49);
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_46, 0);
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_46);
x_52 = lean_ctor_get(x_50, 1);
lean_inc_ref(x_52);
lean_dec(x_50);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_46);
if (x_54 == 0)
{
return x_46;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_46, 0);
x_56 = lean_ctor_get(x_46, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_46);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; 
x_58 = lean_ctor_get(x_37, 0);
x_59 = lean_ctor_get_uint8(x_37, sizeof(void*)*3);
x_60 = lean_ctor_get(x_37, 1);
x_61 = lean_ctor_get(x_37, 2);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_58);
lean_dec(x_37);
x_62 = l_Lake_BuildTrace_mix(x_60, x_38);
x_63 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_61);
lean_ctor_set_uint8(x_63, sizeof(void*)*3, x_59);
x_64 = l_Array_append___redArg(x_4, x_1);
lean_dec_ref(x_1);
lean_inc_ref(x_5);
x_65 = lean_alloc_closure((void*)(l_Lake_buildO___lam__1___boxed), 11, 4);
lean_closure_set(x_65, 0, x_5);
lean_closure_set(x_65, 1, x_9);
lean_closure_set(x_65, 2, x_64);
lean_closure_set(x_65, 3, x_6);
x_66 = 0;
x_67 = l_Lake_buildO___lam__2___closed__2;
x_68 = l_Lake_buildArtifactUnlessUpToDate(x_5, x_65, x_66, x_67, x_66, x_66, x_10, x_11, x_12, x_13, x_14, x_63);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_71 = x_68;
} else {
 lean_dec_ref(x_68);
 x_71 = lean_box(0);
}
x_72 = lean_ctor_get(x_69, 1);
lean_inc_ref(x_72);
lean_dec(x_69);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_68, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_68, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_76 = x_68;
} else {
 lean_dec_ref(x_68);
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
uint8_t x_78; 
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_78 = !lean_is_exclusive(x_36);
if (x_78 == 0)
{
return x_36;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_36, 0);
x_80 = lean_ctor_get(x_36, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_36);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
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
LEAN_EXPORT lean_object* l_Lake_buildO(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_14 = lean_alloc_closure((void*)(l_Lake_buildO___lam__0___boxed), 2, 0);
x_15 = l_Lake_instDataKindFilePath;
x_16 = l_Lake_buildO___closed__0;
x_17 = l_Lake_instMonadWorkspaceJobM___closed__10;
x_18 = lean_alloc_closure((void*)(l_Lake_buildO___lam__2___boxed), 16, 8);
lean_closure_set(x_18, 0, x_4);
lean_closure_set(x_18, 1, x_16);
lean_closure_set(x_18, 2, x_6);
lean_closure_set(x_18, 3, x_3);
lean_closure_set(x_18, 4, x_1);
lean_closure_set(x_18, 5, x_5);
lean_closure_set(x_18, 6, x_17);
lean_closure_set(x_18, 7, x_14);
x_19 = lean_unsigned_to_nat(0u);
x_20 = 0;
x_21 = l_Lake_Job_mapM___redArg(x_15, x_2, x_18, x_19, x_20, x_7, x_8, x_9, x_10, x_11, x_12);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Lake_buildO___lam__0(x_3, x_2);
lean_dec_ref(x_2);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_buildO___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lake_buildO___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lake_buildO(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
static lean_object* _init_l_List_foldl___at___List_toString___at___Lake_buildLeanO_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___List_toString___at___Lake_buildLeanO_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
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
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_List_foldl___at___List_toString___at___Lake_buildLeanO_spec__0_spec__0___closed__0;
x_6 = lean_string_append(x_1, x_5);
x_7 = lean_string_append(x_6, x_3);
x_1 = x_7;
x_2 = x_4;
goto _start;
}
}
}
static lean_object* _init_l_List_toString___at___Lake_buildLeanO_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[]", 2, 2);
return x_1;
}
}
static lean_object* _init_l_List_toString___at___Lake_buildLeanO_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_toString___at___Lake_buildLeanO_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___Lake_buildLeanO_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_toString___at___Lake_buildLeanO_spec__0___closed__0;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_List_toString___at___Lake_buildLeanO_spec__0___closed__1;
x_6 = lean_string_append(x_5, x_4);
x_7 = l_List_toString___at___Lake_buildLeanO_spec__0___closed__2;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = l_List_toString___at___Lake_buildLeanO_spec__0___closed__1;
x_11 = lean_string_append(x_10, x_9);
x_12 = l_List_foldl___at___List_toString___at___Lake_buildLeanO_spec__0_spec__0(x_11, x_3);
x_13 = 93;
x_14 = lean_string_push(x_12, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_buildLeanO_spec__2(lean_object* x_1, size_t x_2, size_t x_3, uint64_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; size_t x_11; size_t x_12; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lake_platformTrace___closed__1;
x_8 = lean_string_hash(x_6);
lean_dec_ref(x_6);
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
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_10, 1);
x_14 = l_Lake_BuildTrace_mix(x_1, x_13);
x_15 = lean_apply_1(x_2, x_11);
x_16 = 1;
lean_ctor_set(x_10, 1, x_14);
x_17 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_15, x_16, x_3, x_4, x_5, x_6, x_7, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_20 = x_17;
} else {
 lean_dec_ref(x_17);
 x_20 = lean_box(0);
}
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_27 = lean_string_utf8_byte_size(x_21);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_dec_eq(x_27, x_28);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_19);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_19, 0);
x_32 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_33 = l_Substring_takeWhileAux___at___Lake_inputBinFile_spec__6(x_21, x_27, x_28);
x_34 = l_Substring_takeRightWhileAux___at___Lake_inputBinFile_spec__7(x_21, x_33, x_27);
x_35 = lean_string_utf8_extract(x_21, x_33, x_34);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_21);
x_36 = lean_string_append(x_32, x_35);
lean_dec_ref(x_35);
x_37 = 1;
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_37);
x_39 = lean_array_push(x_31, x_38);
lean_ctor_set(x_19, 0, x_39);
x_23 = x_19;
x_24 = lean_box(0);
goto block_26;
}
else
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_40 = lean_ctor_get(x_19, 0);
x_41 = lean_ctor_get_uint8(x_19, sizeof(void*)*3);
x_42 = lean_ctor_get(x_19, 1);
x_43 = lean_ctor_get(x_19, 2);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_40);
lean_dec(x_19);
x_44 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_45 = l_Substring_takeWhileAux___at___Lake_inputBinFile_spec__6(x_21, x_27, x_28);
x_46 = l_Substring_takeRightWhileAux___at___Lake_inputBinFile_spec__7(x_21, x_45, x_27);
x_47 = lean_string_utf8_extract(x_21, x_45, x_46);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_21);
x_48 = lean_string_append(x_44, x_47);
lean_dec_ref(x_47);
x_49 = 1;
x_50 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_49);
x_51 = lean_array_push(x_40, x_50);
x_52 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_42);
lean_ctor_set(x_52, 2, x_43);
lean_ctor_set_uint8(x_52, sizeof(void*)*3, x_41);
x_23 = x_52;
x_24 = lean_box(0);
goto block_26;
}
}
else
{
lean_dec(x_27);
lean_dec(x_21);
x_23 = x_19;
x_24 = lean_box(0);
goto block_26;
}
block_26:
{
lean_object* x_25; 
if (lean_is_scalar(x_20)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_20;
}
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_17);
if (x_53 == 0)
{
return x_17;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_17, 0);
x_55 = lean_ctor_get(x_17, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_17);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
x_57 = lean_ctor_get(x_10, 0);
x_58 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
x_59 = lean_ctor_get(x_10, 1);
x_60 = lean_ctor_get(x_10, 2);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_57);
lean_dec(x_10);
x_61 = l_Lake_BuildTrace_mix(x_1, x_59);
x_62 = lean_apply_1(x_2, x_11);
x_63 = 1;
x_64 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_64, 0, x_57);
lean_ctor_set(x_64, 1, x_61);
lean_ctor_set(x_64, 2, x_60);
lean_ctor_set_uint8(x_64, sizeof(void*)*3, x_58);
x_65 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_62, x_63, x_3, x_4, x_5, x_6, x_7, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_68 = x_65;
} else {
 lean_dec_ref(x_65);
 x_68 = lean_box(0);
}
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_66, 1);
lean_inc(x_70);
lean_dec(x_66);
x_75 = lean_string_utf8_byte_size(x_69);
x_76 = lean_unsigned_to_nat(0u);
x_77 = lean_nat_dec_eq(x_75, x_76);
if (x_77 == 0)
{
lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_78 = lean_ctor_get(x_67, 0);
lean_inc_ref(x_78);
x_79 = lean_ctor_get_uint8(x_67, sizeof(void*)*3);
x_80 = lean_ctor_get(x_67, 1);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_67, 2);
lean_inc(x_81);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 lean_ctor_release(x_67, 2);
 x_82 = x_67;
} else {
 lean_dec_ref(x_67);
 x_82 = lean_box(0);
}
x_83 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_84 = l_Substring_takeWhileAux___at___Lake_inputBinFile_spec__6(x_69, x_75, x_76);
x_85 = l_Substring_takeRightWhileAux___at___Lake_inputBinFile_spec__7(x_69, x_84, x_75);
x_86 = lean_string_utf8_extract(x_69, x_84, x_85);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_69);
x_87 = lean_string_append(x_83, x_86);
lean_dec_ref(x_86);
x_88 = 1;
x_89 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set_uint8(x_89, sizeof(void*)*1, x_88);
x_90 = lean_array_push(x_78, x_89);
if (lean_is_scalar(x_82)) {
 x_91 = lean_alloc_ctor(0, 3, 1);
} else {
 x_91 = x_82;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_80);
lean_ctor_set(x_91, 2, x_81);
lean_ctor_set_uint8(x_91, sizeof(void*)*3, x_79);
x_71 = x_91;
x_72 = lean_box(0);
goto block_74;
}
else
{
lean_dec(x_75);
lean_dec(x_69);
x_71 = x_67;
x_72 = lean_box(0);
goto block_74;
}
block_74:
{
lean_object* x_73; 
if (lean_is_scalar(x_68)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_68;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_65, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_65, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_94 = x_65;
} else {
 lean_dec_ref(x_65);
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
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_96 = !lean_is_exclusive(x_8);
if (x_96 == 0)
{
return x_8;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_8, 0);
x_98 = lean_ctor_get(x_8, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_8);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_dec(x_14);
x_15 = lean_alloc_closure((void*)(l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3___redArg___lam__0___boxed), 9, 7);
lean_closure_set(x_15, 0, x_10);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_5);
lean_closure_set(x_15, 3, x_6);
lean_closure_set(x_15, 4, x_7);
lean_closure_set(x_15, 5, x_8);
lean_closure_set(x_15, 6, x_9);
x_16 = lean_io_map_task(x_15, x_13, x_3, x_4);
x_17 = l_Lake_instDataKindFilePath;
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_16);
return x_1;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 2);
x_20 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
x_21 = lean_alloc_closure((void*)(l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3___redArg___lam__0___boxed), 9, 7);
lean_closure_set(x_21, 0, x_10);
lean_closure_set(x_21, 1, x_2);
lean_closure_set(x_21, 2, x_5);
lean_closure_set(x_21, 3, x_6);
lean_closure_set(x_21, 4, x_7);
lean_closure_set(x_21, 5, x_8);
lean_closure_set(x_21, 6, x_9);
x_22 = lean_io_map_task(x_21, x_18, x_3, x_4);
x_23 = l_Lake_instDataKindFilePath;
x_24 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_20);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_17 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_11, 2);
lean_inc(x_18);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 x_19 = x_11;
} else {
 lean_dec_ref(x_11);
 x_19 = lean_box(0);
}
x_20 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_20);
lean_dec_ref(x_14);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_20, 4);
lean_inc_ref(x_45);
x_21 = x_45;
goto block_44;
}
else
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_5, 0);
lean_inc(x_46);
lean_dec_ref(x_5);
x_21 = x_46;
goto block_44;
}
block_44:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_20, 12);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_20, 16);
lean_inc_ref(x_23);
lean_dec_ref(x_20);
x_24 = l_Lake_buildLeanO___lam__0___closed__2;
x_25 = lean_array_push(x_24, x_21);
x_26 = l_Array_append___redArg(x_25, x_23);
lean_dec_ref(x_23);
x_27 = l_Array_append___redArg(x_26, x_1);
x_28 = l_Array_append___redArg(x_27, x_2);
x_29 = l_Lake_compileO(x_3, x_4, x_28, x_22, x_15);
lean_dec_ref(x_28);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 1);
if (lean_is_scalar(x_19)) {
 x_32 = lean_alloc_ctor(0, 3, 1);
} else {
 x_32 = x_19;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_17);
lean_ctor_set(x_32, 2, x_18);
lean_ctor_set_uint8(x_32, sizeof(void*)*3, x_16);
lean_ctor_set(x_29, 1, x_32);
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
if (lean_is_scalar(x_19)) {
 x_35 = lean_alloc_ctor(0, 3, 1);
} else {
 x_35 = x_19;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_17);
lean_ctor_set(x_35, 2, x_18);
lean_ctor_set_uint8(x_35, sizeof(void*)*3, x_16);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_29, 1);
if (lean_is_scalar(x_19)) {
 x_39 = lean_alloc_ctor(0, 3, 1);
} else {
 x_39 = x_19;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_17);
lean_ctor_set(x_39, 2, x_18);
lean_ctor_set_uint8(x_39, sizeof(void*)*3, x_16);
lean_ctor_set(x_29, 1, x_39);
return x_29;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_29, 0);
x_41 = lean_ctor_get(x_29, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_29);
if (lean_is_scalar(x_19)) {
 x_42 = lean_alloc_ctor(0, 3, 1);
} else {
 x_42 = x_19;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_17);
lean_ctor_set(x_42, 2, x_18);
lean_ctor_set_uint8(x_42, sizeof(void*)*3, x_16);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint64_t x_21; uint64_t x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_13);
x_14 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_15 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_11, 2);
lean_inc(x_16);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 x_17 = x_11;
} else {
 lean_dec_ref(x_11);
 x_17 = lean_box(0);
}
x_18 = lean_ctor_get(x_10, 2);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_19 = lean_alloc_closure((void*)(l_Lake_buildLeanO___lam__0___boxed), 12, 5);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_2);
lean_closure_set(x_19, 2, x_3);
lean_closure_set(x_19, 3, x_5);
lean_closure_set(x_19, 4, x_4);
lean_inc_ref(x_18);
x_20 = l_Lake_BuildTrace_mix(x_15, x_18);
x_50 = l_Lake_platformTrace___closed__1;
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_array_get_size(x_2);
x_53 = lean_nat_dec_lt(x_51, x_52);
if (x_53 == 0)
{
lean_dec(x_52);
x_21 = x_50;
goto block_49;
}
else
{
uint8_t x_54; 
x_54 = lean_nat_dec_le(x_52, x_52);
if (x_54 == 0)
{
lean_dec(x_52);
x_21 = x_50;
goto block_49;
}
else
{
size_t x_55; size_t x_56; uint64_t x_57; 
x_55 = 0;
x_56 = lean_usize_of_nat(x_52);
lean_dec(x_52);
x_57 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_buildLeanO_spec__2(x_2, x_55, x_56, x_50);
x_21 = x_57;
goto block_49;
}
}
block_49:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_22 = l_Lake_buildO___lam__2___closed__0;
x_23 = l_Lake_buildO___lam__2___closed__1;
x_24 = lean_array_to_list(x_2);
x_25 = l_List_toString___at___Lake_buildLeanO_spec__0(x_24);
lean_dec(x_24);
x_26 = lean_string_append(x_23, x_25);
lean_dec_ref(x_25);
x_27 = lean_string_append(x_22, x_26);
lean_dec_ref(x_26);
x_28 = l_Lake_platformTrace___closed__4;
x_29 = l_Lake_platformTrace___closed__6;
x_30 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_30, 2, x_29);
lean_ctor_set_uint64(x_30, sizeof(void*)*3, x_21);
x_31 = l_Lake_BuildTrace_mix(x_20, x_30);
x_32 = l_Lake_platformTrace;
x_33 = l_Lake_BuildTrace_mix(x_31, x_32);
if (lean_is_scalar(x_17)) {
 x_34 = lean_alloc_ctor(0, 3, 1);
} else {
 x_34 = x_17;
}
lean_ctor_set(x_34, 0, x_13);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_16);
lean_ctor_set_uint8(x_34, sizeof(void*)*3, x_14);
x_35 = 0;
x_36 = l_Lake_buildO___lam__2___closed__2;
x_37 = l_Lake_buildArtifactUnlessUpToDate(x_3, x_19, x_35, x_36, x_35, x_35, x_6, x_7, x_8, x_9, x_10, x_34);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_39, 1);
lean_inc_ref(x_40);
lean_dec(x_39);
lean_ctor_set(x_37, 0, x_40);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_37, 0);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_37);
x_43 = lean_ctor_get(x_41, 1);
lean_inc_ref(x_43);
lean_dec(x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_37);
if (x_45 == 0)
{
return x_37;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_37, 0);
x_47 = lean_ctor_get(x_37, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_37);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_alloc_closure((void*)(l_Lake_buildLeanO___lam__1___boxed), 12, 4);
lean_closure_set(x_13, 0, x_3);
lean_closure_set(x_13, 1, x_4);
lean_closure_set(x_13, 2, x_1);
lean_closure_set(x_13, 3, x_5);
x_14 = lean_unsigned_to_nat(0u);
x_15 = 0;
x_16 = l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3___redArg(x_2, x_13, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11);
return x_16;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___List_toString___at___Lake_buildLeanO_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at___List_toString___at___Lake_buildLeanO_spec__0_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___Lake_buildLeanO_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_toString___at___Lake_buildLeanO_spec__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_buildLeanO_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_buildLeanO_spec__2(x_1, x_5, x_6, x_7);
lean_dec_ref(x_1);
x_9 = lean_box_uint64(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
x_13 = l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3___redArg(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
x_14 = l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_buildLeanO___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_buildLeanO___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_buildLeanO(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec_ref(x_8);
x_12 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_13);
lean_dec_ref(x_12);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_13, 11);
lean_inc_ref(x_16);
lean_dec_ref(x_13);
x_17 = l_Lake_compileStaticLib(x_1, x_2, x_16, x_3, x_15);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 1);
lean_ctor_set(x_9, 0, x_19);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_17);
lean_ctor_set(x_9, 0, x_21);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_9);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_17, 1);
lean_ctor_set(x_9, 0, x_24);
lean_ctor_set(x_17, 1, x_9);
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
lean_ctor_set(x_9, 0, x_26);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_9);
return x_27;
}
}
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_9, 0);
x_29 = lean_ctor_get_uint8(x_9, sizeof(void*)*3);
x_30 = lean_ctor_get(x_9, 1);
x_31 = lean_ctor_get(x_9, 2);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_28);
lean_dec(x_9);
x_32 = lean_ctor_get(x_13, 11);
lean_inc_ref(x_32);
lean_dec_ref(x_13);
x_33 = l_Lake_compileStaticLib(x_1, x_2, x_32, x_3, x_28);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
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
x_37 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_30);
lean_ctor_set(x_37, 2, x_31);
lean_ctor_set_uint8(x_37, sizeof(void*)*3, x_29);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_33, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_41 = x_33;
} else {
 lean_dec_ref(x_33);
 x_41 = lean_box(0);
}
x_42 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_30);
lean_ctor_set(x_42, 2, x_31);
lean_ctor_set_uint8(x_42, sizeof(void*)*3, x_29);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_42);
return x_43;
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
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_box(x_2);
lean_inc_ref(x_1);
x_12 = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lam__0___boxed), 10, 3);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_11);
x_13 = 0;
x_14 = l_Lake_buildStaticLib___lam__1___closed__0;
x_15 = 1;
x_16 = l_Lake_buildArtifactUnlessUpToDate(x_1, x_12, x_13, x_14, x_15, x_13, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_18, 1);
lean_inc_ref(x_19);
lean_dec(x_18);
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
x_22 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_22);
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
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
static lean_object* _init_l_Lake_buildStaticLib___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("objs", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_11 = lean_box(x_3);
x_12 = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lam__1___boxed), 10, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
x_13 = l_Lake_buildStaticLib___closed__0;
x_14 = l_Lake_Job_collectArray___redArg(x_2, x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = 0;
x_17 = l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3___redArg(x_14, x_12, x_15, x_16, x_4, x_5, x_6, x_7, x_8, x_9);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
x_12 = l_Lake_buildStaticLib___lam__0(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
x_12 = l_Lake_buildStaticLib___lam__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
x_12 = l_Lake_buildStaticLib(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-l", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-L", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_dec_ref(x_16);
x_18 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1;
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
lean_inc_ref(x_8);
lean_dec_ref(x_6);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0;
x_10 = lean_string_append(x_9, x_8);
lean_dec_ref(x_8);
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
x_3 = l_Lake_inputDir___lam__1___closed__0;
x_4 = lean_array_size(x_1);
x_5 = 0;
x_6 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(x_1, x_4, x_5, x_3);
x_7 = lean_array_size(x_2);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(x_2, x_7, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_2, 4);
x_6 = lean_string_dec_lt(x_1, x_3);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = lean_string_dec_eq(x_1, x_3);
if (x_7 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_7;
}
}
else
{
x_2 = x_4;
goto _start;
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_List_elem___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(lean_object* x_1, lean_object* x_2) {
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
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_string_dec_eq(x_1, x_4);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
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
lean_dec_ref(x_5);
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
lean_dec_ref(x_10);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = lean_string_dec_lt(x_1, x_5);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = lean_string_dec_eq(x_1, x_5);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_12 = l_Std_DTreeMap_Internal_Impl_insert___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(x_1, x_2, x_8);
x_13 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_12, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_12, 4);
lean_inc(x_19);
x_20 = lean_unsigned_to_nat(3u);
x_21 = lean_nat_mul(x_20, x_14);
x_22 = lean_nat_dec_lt(x_21, x_15);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_23 = lean_nat_add(x_13, x_14);
x_24 = lean_nat_add(x_23, x_15);
lean_dec(x_15);
lean_dec(x_23);
if (lean_is_scalar(x_9)) {
 x_25 = lean_alloc_ctor(0, 5, 0);
} else {
 x_25 = x_9;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_5);
lean_ctor_set(x_25, 2, x_6);
lean_ctor_set(x_25, 3, x_7);
lean_ctor_set(x_25, 4, x_12);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 x_26 = x_12;
} else {
 lean_dec_ref(x_12);
 x_26 = lean_box(0);
}
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
x_29 = lean_ctor_get(x_18, 2);
x_30 = lean_ctor_get(x_18, 3);
x_31 = lean_ctor_get(x_18, 4);
x_32 = lean_ctor_get(x_19, 0);
x_33 = lean_unsigned_to_nat(2u);
x_34 = lean_nat_mul(x_33, x_32);
x_35 = lean_nat_dec_lt(x_27, x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_46; 
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
 x_36 = x_18;
} else {
 lean_dec_ref(x_18);
 x_36 = lean_box(0);
}
x_37 = lean_nat_add(x_13, x_14);
x_38 = lean_nat_add(x_37, x_15);
lean_dec(x_15);
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
block_45:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_nat_add(x_39, x_41);
lean_dec(x_41);
lean_dec(x_39);
if (lean_is_scalar(x_36)) {
 x_43 = lean_alloc_ctor(0, 5, 0);
} else {
 x_43 = x_36;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_16);
lean_ctor_set(x_43, 2, x_17);
lean_ctor_set(x_43, 3, x_31);
lean_ctor_set(x_43, 4, x_19);
if (lean_is_scalar(x_26)) {
 x_44 = lean_alloc_ctor(0, 5, 0);
} else {
 x_44 = x_26;
}
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_28);
lean_ctor_set(x_44, 2, x_29);
lean_ctor_set(x_44, 3, x_40);
lean_ctor_set(x_44, 4, x_43);
return x_44;
}
block_52:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_nat_add(x_37, x_46);
lean_dec(x_46);
lean_dec(x_37);
if (lean_is_scalar(x_9)) {
 x_48 = lean_alloc_ctor(0, 5, 0);
} else {
 x_48 = x_9;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_5);
lean_ctor_set(x_48, 2, x_6);
lean_ctor_set(x_48, 3, x_7);
lean_ctor_set(x_48, 4, x_30);
x_49 = lean_nat_add(x_13, x_32);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_31, 0);
lean_inc(x_50);
x_39 = x_49;
x_40 = x_48;
x_41 = x_50;
goto block_45;
}
else
{
lean_object* x_51; 
x_51 = lean_unsigned_to_nat(0u);
x_39 = x_49;
x_40 = x_48;
x_41 = x_51;
goto block_45;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_9);
x_55 = lean_nat_add(x_13, x_14);
x_56 = lean_nat_add(x_55, x_15);
lean_dec(x_15);
x_57 = lean_nat_add(x_55, x_27);
lean_dec(x_55);
lean_inc_ref(x_7);
if (lean_is_scalar(x_26)) {
 x_58 = lean_alloc_ctor(0, 5, 0);
} else {
 x_58 = x_26;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_5);
lean_ctor_set(x_58, 2, x_6);
lean_ctor_set(x_58, 3, x_7);
lean_ctor_set(x_58, 4, x_18);
x_59 = !lean_is_exclusive(x_7);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_7, 4);
lean_dec(x_60);
x_61 = lean_ctor_get(x_7, 3);
lean_dec(x_61);
x_62 = lean_ctor_get(x_7, 2);
lean_dec(x_62);
x_63 = lean_ctor_get(x_7, 1);
lean_dec(x_63);
x_64 = lean_ctor_get(x_7, 0);
lean_dec(x_64);
lean_ctor_set(x_7, 4, x_19);
lean_ctor_set(x_7, 3, x_58);
lean_ctor_set(x_7, 2, x_17);
lean_ctor_set(x_7, 1, x_16);
lean_ctor_set(x_7, 0, x_56);
return x_7;
}
else
{
lean_object* x_65; 
lean_dec(x_7);
x_65 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_65, 0, x_56);
lean_ctor_set(x_65, 1, x_16);
lean_ctor_set(x_65, 2, x_17);
lean_ctor_set(x_65, 3, x_58);
lean_ctor_set(x_65, 4, x_19);
return x_65;
}
}
}
}
else
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_12, 3);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_12);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_68 = lean_ctor_get(x_12, 4);
x_69 = lean_ctor_get(x_12, 3);
lean_dec(x_69);
x_70 = lean_ctor_get(x_12, 0);
lean_dec(x_70);
x_71 = !lean_is_exclusive(x_66);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_72 = lean_ctor_get(x_66, 1);
x_73 = lean_ctor_get(x_66, 2);
x_74 = lean_ctor_get(x_66, 4);
lean_dec(x_74);
x_75 = lean_ctor_get(x_66, 3);
lean_dec(x_75);
x_76 = lean_ctor_get(x_66, 0);
lean_dec(x_76);
x_77 = lean_unsigned_to_nat(3u);
lean_inc_n(x_68, 2);
lean_ctor_set(x_66, 4, x_68);
lean_ctor_set(x_66, 3, x_68);
lean_ctor_set(x_66, 2, x_6);
lean_ctor_set(x_66, 1, x_5);
lean_ctor_set(x_66, 0, x_13);
lean_inc(x_68);
lean_ctor_set(x_12, 3, x_68);
lean_ctor_set(x_12, 0, x_13);
if (lean_is_scalar(x_9)) {
 x_78 = lean_alloc_ctor(0, 5, 0);
} else {
 x_78 = x_9;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_72);
lean_ctor_set(x_78, 2, x_73);
lean_ctor_set(x_78, 3, x_66);
lean_ctor_set(x_78, 4, x_12);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_ctor_get(x_66, 1);
x_80 = lean_ctor_get(x_66, 2);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_66);
x_81 = lean_unsigned_to_nat(3u);
lean_inc_n(x_68, 2);
x_82 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_82, 0, x_13);
lean_ctor_set(x_82, 1, x_5);
lean_ctor_set(x_82, 2, x_6);
lean_ctor_set(x_82, 3, x_68);
lean_ctor_set(x_82, 4, x_68);
lean_inc(x_68);
lean_ctor_set(x_12, 3, x_68);
lean_ctor_set(x_12, 0, x_13);
if (lean_is_scalar(x_9)) {
 x_83 = lean_alloc_ctor(0, 5, 0);
} else {
 x_83 = x_9;
}
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_79);
lean_ctor_set(x_83, 2, x_80);
lean_ctor_set(x_83, 3, x_82);
lean_ctor_set(x_83, 4, x_12);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_84 = lean_ctor_get(x_12, 4);
x_85 = lean_ctor_get(x_12, 1);
x_86 = lean_ctor_get(x_12, 2);
lean_inc(x_84);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_12);
x_87 = lean_ctor_get(x_66, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_66, 2);
lean_inc(x_88);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 lean_ctor_release(x_66, 2);
 lean_ctor_release(x_66, 3);
 lean_ctor_release(x_66, 4);
 x_89 = x_66;
} else {
 lean_dec_ref(x_66);
 x_89 = lean_box(0);
}
x_90 = lean_unsigned_to_nat(3u);
lean_inc_n(x_84, 2);
if (lean_is_scalar(x_89)) {
 x_91 = lean_alloc_ctor(0, 5, 0);
} else {
 x_91 = x_89;
}
lean_ctor_set(x_91, 0, x_13);
lean_ctor_set(x_91, 1, x_5);
lean_ctor_set(x_91, 2, x_6);
lean_ctor_set(x_91, 3, x_84);
lean_ctor_set(x_91, 4, x_84);
lean_inc(x_84);
x_92 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_92, 0, x_13);
lean_ctor_set(x_92, 1, x_85);
lean_ctor_set(x_92, 2, x_86);
lean_ctor_set(x_92, 3, x_84);
lean_ctor_set(x_92, 4, x_84);
if (lean_is_scalar(x_9)) {
 x_93 = lean_alloc_ctor(0, 5, 0);
} else {
 x_93 = x_9;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_87);
lean_ctor_set(x_93, 2, x_88);
lean_ctor_set(x_93, 3, x_91);
lean_ctor_set(x_93, 4, x_92);
return x_93;
}
}
else
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_12, 4);
lean_inc(x_94);
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_12);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_96 = lean_ctor_get(x_12, 1);
x_97 = lean_ctor_get(x_12, 2);
x_98 = lean_ctor_get(x_12, 4);
lean_dec(x_98);
x_99 = lean_ctor_get(x_12, 3);
lean_dec(x_99);
x_100 = lean_ctor_get(x_12, 0);
lean_dec(x_100);
x_101 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_12, 4, x_66);
lean_ctor_set(x_12, 2, x_6);
lean_ctor_set(x_12, 1, x_5);
lean_ctor_set(x_12, 0, x_13);
if (lean_is_scalar(x_9)) {
 x_102 = lean_alloc_ctor(0, 5, 0);
} else {
 x_102 = x_9;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_96);
lean_ctor_set(x_102, 2, x_97);
lean_ctor_set(x_102, 3, x_12);
lean_ctor_set(x_102, 4, x_94);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_ctor_get(x_12, 1);
x_104 = lean_ctor_get(x_12, 2);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_12);
x_105 = lean_unsigned_to_nat(3u);
x_106 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_106, 0, x_13);
lean_ctor_set(x_106, 1, x_5);
lean_ctor_set(x_106, 2, x_6);
lean_ctor_set(x_106, 3, x_66);
lean_ctor_set(x_106, 4, x_66);
if (lean_is_scalar(x_9)) {
 x_107 = lean_alloc_ctor(0, 5, 0);
} else {
 x_107 = x_9;
}
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_103);
lean_ctor_set(x_107, 2, x_104);
lean_ctor_set(x_107, 3, x_106);
lean_ctor_set(x_107, 4, x_94);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_9)) {
 x_109 = lean_alloc_ctor(0, 5, 0);
} else {
 x_109 = x_9;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_5);
lean_ctor_set(x_109, 2, x_6);
lean_ctor_set(x_109, 3, x_94);
lean_ctor_set(x_109, 4, x_12);
return x_109;
}
}
}
}
else
{
lean_object* x_110; 
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_9)) {
 x_110 = lean_alloc_ctor(0, 5, 0);
} else {
 x_110 = x_9;
}
lean_ctor_set(x_110, 0, x_4);
lean_ctor_set(x_110, 1, x_1);
lean_ctor_set(x_110, 2, x_2);
lean_ctor_set(x_110, 3, x_7);
lean_ctor_set(x_110, 4, x_8);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_4);
x_111 = l_Std_DTreeMap_Internal_Impl_insert___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(x_1, x_2, x_7);
x_112 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_113 = lean_ctor_get(x_8, 0);
x_114 = lean_ctor_get(x_111, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_111, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_111, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_111, 3);
lean_inc(x_117);
x_118 = lean_ctor_get(x_111, 4);
lean_inc(x_118);
x_119 = lean_unsigned_to_nat(3u);
x_120 = lean_nat_mul(x_119, x_113);
x_121 = lean_nat_dec_lt(x_120, x_114);
lean_dec(x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_115);
x_122 = lean_nat_add(x_112, x_114);
lean_dec(x_114);
x_123 = lean_nat_add(x_122, x_113);
lean_dec(x_122);
if (lean_is_scalar(x_9)) {
 x_124 = lean_alloc_ctor(0, 5, 0);
} else {
 x_124 = x_9;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_5);
lean_ctor_set(x_124, 2, x_6);
lean_ctor_set(x_124, 3, x_111);
lean_ctor_set(x_124, 4, x_8);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 lean_ctor_release(x_111, 2);
 lean_ctor_release(x_111, 3);
 lean_ctor_release(x_111, 4);
 x_125 = x_111;
} else {
 lean_dec_ref(x_111);
 x_125 = lean_box(0);
}
x_126 = lean_ctor_get(x_117, 0);
x_127 = lean_ctor_get(x_118, 0);
x_128 = lean_ctor_get(x_118, 1);
x_129 = lean_ctor_get(x_118, 2);
x_130 = lean_ctor_get(x_118, 3);
x_131 = lean_ctor_get(x_118, 4);
x_132 = lean_unsigned_to_nat(2u);
x_133 = lean_nat_mul(x_132, x_126);
x_134 = lean_nat_dec_lt(x_127, x_133);
lean_dec(x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_145; lean_object* x_146; 
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 lean_ctor_release(x_118, 2);
 lean_ctor_release(x_118, 3);
 lean_ctor_release(x_118, 4);
 x_135 = x_118;
} else {
 lean_dec_ref(x_118);
 x_135 = lean_box(0);
}
x_136 = lean_nat_add(x_112, x_114);
lean_dec(x_114);
x_137 = lean_nat_add(x_136, x_113);
lean_dec(x_136);
x_145 = lean_nat_add(x_112, x_126);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_130, 0);
lean_inc(x_153);
x_146 = x_153;
goto block_152;
}
else
{
lean_object* x_154; 
x_154 = lean_unsigned_to_nat(0u);
x_146 = x_154;
goto block_152;
}
block_144:
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_nat_add(x_139, x_140);
lean_dec(x_140);
lean_dec(x_139);
if (lean_is_scalar(x_135)) {
 x_142 = lean_alloc_ctor(0, 5, 0);
} else {
 x_142 = x_135;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_5);
lean_ctor_set(x_142, 2, x_6);
lean_ctor_set(x_142, 3, x_131);
lean_ctor_set(x_142, 4, x_8);
if (lean_is_scalar(x_125)) {
 x_143 = lean_alloc_ctor(0, 5, 0);
} else {
 x_143 = x_125;
}
lean_ctor_set(x_143, 0, x_137);
lean_ctor_set(x_143, 1, x_128);
lean_ctor_set(x_143, 2, x_129);
lean_ctor_set(x_143, 3, x_138);
lean_ctor_set(x_143, 4, x_142);
return x_143;
}
block_152:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_nat_add(x_145, x_146);
lean_dec(x_146);
lean_dec(x_145);
if (lean_is_scalar(x_9)) {
 x_148 = lean_alloc_ctor(0, 5, 0);
} else {
 x_148 = x_9;
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_115);
lean_ctor_set(x_148, 2, x_116);
lean_ctor_set(x_148, 3, x_117);
lean_ctor_set(x_148, 4, x_130);
x_149 = lean_nat_add(x_112, x_113);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_131, 0);
lean_inc(x_150);
x_138 = x_148;
x_139 = x_149;
x_140 = x_150;
goto block_144;
}
else
{
lean_object* x_151; 
x_151 = lean_unsigned_to_nat(0u);
x_138 = x_148;
x_139 = x_149;
x_140 = x_151;
goto block_144;
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
lean_dec(x_9);
x_155 = lean_nat_add(x_112, x_114);
lean_dec(x_114);
x_156 = lean_nat_add(x_155, x_113);
lean_dec(x_155);
x_157 = lean_nat_add(x_112, x_113);
x_158 = lean_nat_add(x_157, x_127);
lean_dec(x_157);
lean_inc_ref(x_8);
if (lean_is_scalar(x_125)) {
 x_159 = lean_alloc_ctor(0, 5, 0);
} else {
 x_159 = x_125;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_5);
lean_ctor_set(x_159, 2, x_6);
lean_ctor_set(x_159, 3, x_118);
lean_ctor_set(x_159, 4, x_8);
x_160 = !lean_is_exclusive(x_8);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_161 = lean_ctor_get(x_8, 4);
lean_dec(x_161);
x_162 = lean_ctor_get(x_8, 3);
lean_dec(x_162);
x_163 = lean_ctor_get(x_8, 2);
lean_dec(x_163);
x_164 = lean_ctor_get(x_8, 1);
lean_dec(x_164);
x_165 = lean_ctor_get(x_8, 0);
lean_dec(x_165);
lean_ctor_set(x_8, 4, x_159);
lean_ctor_set(x_8, 3, x_117);
lean_ctor_set(x_8, 2, x_116);
lean_ctor_set(x_8, 1, x_115);
lean_ctor_set(x_8, 0, x_156);
return x_8;
}
else
{
lean_object* x_166; 
lean_dec(x_8);
x_166 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_166, 0, x_156);
lean_ctor_set(x_166, 1, x_115);
lean_ctor_set(x_166, 2, x_116);
lean_ctor_set(x_166, 3, x_117);
lean_ctor_set(x_166, 4, x_159);
return x_166;
}
}
}
}
else
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_111, 3);
lean_inc(x_167);
if (lean_obj_tag(x_167) == 0)
{
uint8_t x_168; 
x_168 = !lean_is_exclusive(x_111);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_169 = lean_ctor_get(x_111, 4);
x_170 = lean_ctor_get(x_111, 1);
x_171 = lean_ctor_get(x_111, 2);
x_172 = lean_ctor_get(x_111, 3);
lean_dec(x_172);
x_173 = lean_ctor_get(x_111, 0);
lean_dec(x_173);
x_174 = lean_unsigned_to_nat(3u);
lean_inc(x_169);
lean_ctor_set(x_111, 3, x_169);
lean_ctor_set(x_111, 2, x_6);
lean_ctor_set(x_111, 1, x_5);
lean_ctor_set(x_111, 0, x_112);
if (lean_is_scalar(x_9)) {
 x_175 = lean_alloc_ctor(0, 5, 0);
} else {
 x_175 = x_9;
}
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_170);
lean_ctor_set(x_175, 2, x_171);
lean_ctor_set(x_175, 3, x_167);
lean_ctor_set(x_175, 4, x_111);
return x_175;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_176 = lean_ctor_get(x_111, 4);
x_177 = lean_ctor_get(x_111, 1);
x_178 = lean_ctor_get(x_111, 2);
lean_inc(x_176);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_111);
x_179 = lean_unsigned_to_nat(3u);
lean_inc(x_176);
x_180 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_180, 0, x_112);
lean_ctor_set(x_180, 1, x_5);
lean_ctor_set(x_180, 2, x_6);
lean_ctor_set(x_180, 3, x_176);
lean_ctor_set(x_180, 4, x_176);
if (lean_is_scalar(x_9)) {
 x_181 = lean_alloc_ctor(0, 5, 0);
} else {
 x_181 = x_9;
}
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_177);
lean_ctor_set(x_181, 2, x_178);
lean_ctor_set(x_181, 3, x_167);
lean_ctor_set(x_181, 4, x_180);
return x_181;
}
}
else
{
lean_object* x_182; 
x_182 = lean_ctor_get(x_111, 4);
lean_inc(x_182);
if (lean_obj_tag(x_182) == 0)
{
uint8_t x_183; 
x_183 = !lean_is_exclusive(x_111);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_184 = lean_ctor_get(x_111, 1);
x_185 = lean_ctor_get(x_111, 2);
x_186 = lean_ctor_get(x_111, 4);
lean_dec(x_186);
x_187 = lean_ctor_get(x_111, 3);
lean_dec(x_187);
x_188 = lean_ctor_get(x_111, 0);
lean_dec(x_188);
x_189 = !lean_is_exclusive(x_182);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_190 = lean_ctor_get(x_182, 1);
x_191 = lean_ctor_get(x_182, 2);
x_192 = lean_ctor_get(x_182, 4);
lean_dec(x_192);
x_193 = lean_ctor_get(x_182, 3);
lean_dec(x_193);
x_194 = lean_ctor_get(x_182, 0);
lean_dec(x_194);
x_195 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_182, 4, x_167);
lean_ctor_set(x_182, 3, x_167);
lean_ctor_set(x_182, 2, x_185);
lean_ctor_set(x_182, 1, x_184);
lean_ctor_set(x_182, 0, x_112);
lean_ctor_set(x_111, 4, x_167);
lean_ctor_set(x_111, 2, x_6);
lean_ctor_set(x_111, 1, x_5);
lean_ctor_set(x_111, 0, x_112);
if (lean_is_scalar(x_9)) {
 x_196 = lean_alloc_ctor(0, 5, 0);
} else {
 x_196 = x_9;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_190);
lean_ctor_set(x_196, 2, x_191);
lean_ctor_set(x_196, 3, x_182);
lean_ctor_set(x_196, 4, x_111);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_197 = lean_ctor_get(x_182, 1);
x_198 = lean_ctor_get(x_182, 2);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_182);
x_199 = lean_unsigned_to_nat(3u);
x_200 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_200, 0, x_112);
lean_ctor_set(x_200, 1, x_184);
lean_ctor_set(x_200, 2, x_185);
lean_ctor_set(x_200, 3, x_167);
lean_ctor_set(x_200, 4, x_167);
lean_ctor_set(x_111, 4, x_167);
lean_ctor_set(x_111, 2, x_6);
lean_ctor_set(x_111, 1, x_5);
lean_ctor_set(x_111, 0, x_112);
if (lean_is_scalar(x_9)) {
 x_201 = lean_alloc_ctor(0, 5, 0);
} else {
 x_201 = x_9;
}
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_197);
lean_ctor_set(x_201, 2, x_198);
lean_ctor_set(x_201, 3, x_200);
lean_ctor_set(x_201, 4, x_111);
return x_201;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_202 = lean_ctor_get(x_111, 1);
x_203 = lean_ctor_get(x_111, 2);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_111);
x_204 = lean_ctor_get(x_182, 1);
lean_inc(x_204);
x_205 = lean_ctor_get(x_182, 2);
lean_inc(x_205);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 lean_ctor_release(x_182, 2);
 lean_ctor_release(x_182, 3);
 lean_ctor_release(x_182, 4);
 x_206 = x_182;
} else {
 lean_dec_ref(x_182);
 x_206 = lean_box(0);
}
x_207 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_206)) {
 x_208 = lean_alloc_ctor(0, 5, 0);
} else {
 x_208 = x_206;
}
lean_ctor_set(x_208, 0, x_112);
lean_ctor_set(x_208, 1, x_202);
lean_ctor_set(x_208, 2, x_203);
lean_ctor_set(x_208, 3, x_167);
lean_ctor_set(x_208, 4, x_167);
x_209 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_209, 0, x_112);
lean_ctor_set(x_209, 1, x_5);
lean_ctor_set(x_209, 2, x_6);
lean_ctor_set(x_209, 3, x_167);
lean_ctor_set(x_209, 4, x_167);
if (lean_is_scalar(x_9)) {
 x_210 = lean_alloc_ctor(0, 5, 0);
} else {
 x_210 = x_9;
}
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_204);
lean_ctor_set(x_210, 2, x_205);
lean_ctor_set(x_210, 3, x_208);
lean_ctor_set(x_210, 4, x_209);
return x_210;
}
}
else
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_9)) {
 x_212 = lean_alloc_ctor(0, 5, 0);
} else {
 x_212 = x_9;
}
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_5);
lean_ctor_set(x_212, 2, x_6);
lean_ctor_set(x_212, 3, x_111);
lean_ctor_set(x_212, 4, x_182);
return x_212;
}
}
}
}
}
else
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_unsigned_to_nat(1u);
x_214 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_1);
lean_ctor_set(x_214, 2, x_2);
lean_ctor_set(x_214, 3, x_3);
lean_ctor_set(x_214, 4, x_3);
return x_214;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_insert___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_6);
x_7 = lean_array_push(x_4, x_1);
x_8 = l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(x_5, x_3);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_List_elem___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(x_5, x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_inc_ref(x_5);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_2);
if (x_8 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = l_Std_DTreeMap_Internal_Impl_insert___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(x_5, x_23, x_3);
x_11 = x_24;
goto block_22;
}
else
{
lean_dec_ref(x_5);
x_11 = x_3;
goto block_22;
}
block_22:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
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
lean_dec_ref(x_10);
lean_dec_ref(x_6);
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
lean_dec_ref(x_10);
lean_dec_ref(x_6);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_12);
return x_18;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_21 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(x_10, x_6, x_19, x_20, x_12);
lean_dec_ref(x_6);
return x_21;
}
}
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_2);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_7);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_elem___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_dec_ref(x_4);
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
lean_dec_ref(x_10);
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
x_2 = lean_box(1);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0;
x_9 = lean_array_get_size(x_1);
x_10 = lean_nat_dec_lt(x_7, x_9);
if (x_10 == 0)
{
lean_dec(x_9);
x_4 = x_8;
goto block_6;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_9, x_9);
if (x_11 == 0)
{
lean_dec(x_9);
x_4 = x_8;
goto block_6;
}
else
{
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1;
x_13 = 0;
x_14 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0(x_1, x_13, x_14, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2;
x_20 = l_Lake_formatCycle___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(x_16);
x_21 = lean_string_append(x_19, x_20);
lean_dec_ref(x_20);
x_22 = 3;
x_23 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_22);
x_24 = lean_array_get_size(x_18);
x_25 = lean_array_push(x_18, x_23);
lean_ctor_set(x_2, 0, x_25);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_2);
return x_26;
}
else
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get(x_2, 0);
x_28 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_29 = lean_ctor_get(x_2, 1);
x_30 = lean_ctor_get(x_2, 2);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_27);
lean_dec(x_2);
x_31 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2;
x_32 = l_Lake_formatCycle___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(x_16);
x_33 = lean_string_append(x_31, x_32);
lean_dec_ref(x_32);
x_34 = 3;
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
x_36 = lean_array_get_size(x_27);
x_37 = lean_array_push(x_27, x_35);
x_38 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_29);
lean_ctor_set(x_38, 2, x_30);
lean_ctor_set_uint8(x_38, sizeof(void*)*3, x_28);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec_ref(x_15);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_4 = x_41;
goto block_6;
}
}
}
block_6:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(x_1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_10, 1);
x_14 = l_Lake_BuildTrace_mix(x_1, x_13);
x_15 = lean_apply_1(x_2, x_11);
x_16 = 1;
lean_ctor_set(x_10, 1, x_14);
x_17 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_15, x_16, x_3, x_4, x_5, x_6, x_7, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_20 = x_17;
} else {
 lean_dec_ref(x_17);
 x_20 = lean_box(0);
}
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_27 = lean_string_utf8_byte_size(x_21);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_dec_eq(x_27, x_28);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_19);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_19, 0);
x_32 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_33 = l_Substring_takeWhileAux___at___Lake_inputBinFile_spec__6(x_21, x_27, x_28);
x_34 = l_Substring_takeRightWhileAux___at___Lake_inputBinFile_spec__7(x_21, x_33, x_27);
x_35 = lean_string_utf8_extract(x_21, x_33, x_34);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_21);
x_36 = lean_string_append(x_32, x_35);
lean_dec_ref(x_35);
x_37 = 1;
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_37);
x_39 = lean_array_push(x_31, x_38);
lean_ctor_set(x_19, 0, x_39);
x_23 = x_19;
x_24 = lean_box(0);
goto block_26;
}
else
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_40 = lean_ctor_get(x_19, 0);
x_41 = lean_ctor_get_uint8(x_19, sizeof(void*)*3);
x_42 = lean_ctor_get(x_19, 1);
x_43 = lean_ctor_get(x_19, 2);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_40);
lean_dec(x_19);
x_44 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_45 = l_Substring_takeWhileAux___at___Lake_inputBinFile_spec__6(x_21, x_27, x_28);
x_46 = l_Substring_takeRightWhileAux___at___Lake_inputBinFile_spec__7(x_21, x_45, x_27);
x_47 = lean_string_utf8_extract(x_21, x_45, x_46);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_21);
x_48 = lean_string_append(x_44, x_47);
lean_dec_ref(x_47);
x_49 = 1;
x_50 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_49);
x_51 = lean_array_push(x_40, x_50);
x_52 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_42);
lean_ctor_set(x_52, 2, x_43);
lean_ctor_set_uint8(x_52, sizeof(void*)*3, x_41);
x_23 = x_52;
x_24 = lean_box(0);
goto block_26;
}
}
else
{
lean_dec(x_27);
lean_dec(x_21);
x_23 = x_19;
x_24 = lean_box(0);
goto block_26;
}
block_26:
{
lean_object* x_25; 
if (lean_is_scalar(x_20)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_20;
}
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_17);
if (x_53 == 0)
{
return x_17;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_17, 0);
x_55 = lean_ctor_get(x_17, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_17);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
x_57 = lean_ctor_get(x_10, 0);
x_58 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
x_59 = lean_ctor_get(x_10, 1);
x_60 = lean_ctor_get(x_10, 2);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_57);
lean_dec(x_10);
x_61 = l_Lake_BuildTrace_mix(x_1, x_59);
x_62 = lean_apply_1(x_2, x_11);
x_63 = 1;
x_64 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_64, 0, x_57);
lean_ctor_set(x_64, 1, x_61);
lean_ctor_set(x_64, 2, x_60);
lean_ctor_set_uint8(x_64, sizeof(void*)*3, x_58);
x_65 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_62, x_63, x_3, x_4, x_5, x_6, x_7, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_68 = x_65;
} else {
 lean_dec_ref(x_65);
 x_68 = lean_box(0);
}
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_66, 1);
lean_inc(x_70);
lean_dec(x_66);
x_75 = lean_string_utf8_byte_size(x_69);
x_76 = lean_unsigned_to_nat(0u);
x_77 = lean_nat_dec_eq(x_75, x_76);
if (x_77 == 0)
{
lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_78 = lean_ctor_get(x_67, 0);
lean_inc_ref(x_78);
x_79 = lean_ctor_get_uint8(x_67, sizeof(void*)*3);
x_80 = lean_ctor_get(x_67, 1);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_67, 2);
lean_inc(x_81);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 lean_ctor_release(x_67, 2);
 x_82 = x_67;
} else {
 lean_dec_ref(x_67);
 x_82 = lean_box(0);
}
x_83 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_84 = l_Substring_takeWhileAux___at___Lake_inputBinFile_spec__6(x_69, x_75, x_76);
x_85 = l_Substring_takeRightWhileAux___at___Lake_inputBinFile_spec__7(x_69, x_84, x_75);
x_86 = lean_string_utf8_extract(x_69, x_84, x_85);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_69);
x_87 = lean_string_append(x_83, x_86);
lean_dec_ref(x_86);
x_88 = 1;
x_89 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set_uint8(x_89, sizeof(void*)*1, x_88);
x_90 = lean_array_push(x_78, x_89);
if (lean_is_scalar(x_82)) {
 x_91 = lean_alloc_ctor(0, 3, 1);
} else {
 x_91 = x_82;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_80);
lean_ctor_set(x_91, 2, x_81);
lean_ctor_set_uint8(x_91, sizeof(void*)*3, x_79);
x_71 = x_91;
x_72 = lean_box(0);
goto block_74;
}
else
{
lean_dec(x_75);
lean_dec(x_69);
x_71 = x_67;
x_72 = lean_box(0);
goto block_74;
}
block_74:
{
lean_object* x_73; 
if (lean_is_scalar(x_68)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_68;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_65, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_65, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_94 = x_65;
} else {
 lean_dec_ref(x_65);
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
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_96 = !lean_is_exclusive(x_8);
if (x_96 == 0)
{
return x_8;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_8, 0);
x_98 = lean_ctor_get(x_8, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_8);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_dec(x_14);
x_15 = lean_alloc_closure((void*)(l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___redArg___lam__0___boxed), 9, 7);
lean_closure_set(x_15, 0, x_10);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_5);
lean_closure_set(x_15, 3, x_6);
lean_closure_set(x_15, 4, x_7);
lean_closure_set(x_15, 5, x_8);
lean_closure_set(x_15, 6, x_9);
x_16 = lean_io_map_task(x_15, x_13, x_3, x_4);
x_17 = l_Lake_instDataKindDynlib;
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_16);
return x_1;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 2);
x_20 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
x_21 = lean_alloc_closure((void*)(l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___redArg___lam__0___boxed), 9, 7);
lean_closure_set(x_21, 0, x_10);
lean_closure_set(x_21, 1, x_2);
lean_closure_set(x_21, 2, x_5);
lean_closure_set(x_21, 3, x_6);
lean_closure_set(x_21, 4, x_7);
lean_closure_set(x_21, 5, x_8);
lean_closure_set(x_21, 6, x_9);
x_22 = lean_io_map_task(x_21, x_18, x_3, x_4);
x_23 = l_Lake_instDataKindDynlib;
x_24 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_20);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_17; 
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_9, 0);
lean_inc(x_26);
lean_dec_ref(x_9);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_25, 1);
x_29 = l_Lake_BuildTrace_mix(x_1, x_28);
x_30 = lean_apply_1(x_2, x_26);
x_31 = 1;
lean_ctor_set(x_25, 1, x_29);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_32 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_30, x_31, x_3, x_4, x_5, x_6, x_7, x_25);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_string_utf8_byte_size(x_35);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_nat_dec_eq(x_37, x_38);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_34);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_41 = lean_ctor_get(x_34, 0);
x_42 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_43 = l_Substring_takeWhileAux___at___Lake_inputBinFile_spec__6(x_35, x_37, x_38);
x_44 = l_Substring_takeRightWhileAux___at___Lake_inputBinFile_spec__7(x_35, x_43, x_37);
x_45 = lean_string_utf8_extract(x_35, x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_35);
x_46 = lean_string_append(x_42, x_45);
lean_dec_ref(x_45);
x_47 = 1;
x_48 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_47);
x_49 = lean_box(0);
x_50 = lean_array_push(x_41, x_48);
lean_ctor_set(x_34, 0, x_50);
x_51 = l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__1(x_36, x_49, x_3, x_4, x_5, x_6, x_7, x_34);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_17 = x_51;
goto block_24;
}
else
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_52 = lean_ctor_get(x_34, 0);
x_53 = lean_ctor_get_uint8(x_34, sizeof(void*)*3);
x_54 = lean_ctor_get(x_34, 1);
x_55 = lean_ctor_get(x_34, 2);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_52);
lean_dec(x_34);
x_56 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_57 = l_Substring_takeWhileAux___at___Lake_inputBinFile_spec__6(x_35, x_37, x_38);
x_58 = l_Substring_takeRightWhileAux___at___Lake_inputBinFile_spec__7(x_35, x_57, x_37);
x_59 = lean_string_utf8_extract(x_35, x_57, x_58);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_35);
x_60 = lean_string_append(x_56, x_59);
lean_dec_ref(x_59);
x_61 = 1;
x_62 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_61);
x_63 = lean_box(0);
x_64 = lean_array_push(x_52, x_62);
x_65 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_54);
lean_ctor_set(x_65, 2, x_55);
lean_ctor_set_uint8(x_65, sizeof(void*)*3, x_53);
x_66 = l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__1(x_36, x_63, x_3, x_4, x_5, x_6, x_7, x_65);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_17 = x_66;
goto block_24;
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_37);
lean_dec(x_35);
x_67 = lean_box(0);
x_68 = l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__1(x_36, x_67, x_3, x_4, x_5, x_6, x_7, x_34);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_17 = x_68;
goto block_24;
}
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_69 = lean_ctor_get(x_32, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_32, 1);
lean_inc(x_70);
lean_dec_ref(x_32);
x_11 = x_69;
x_12 = x_70;
x_13 = lean_box(0);
goto block_16;
}
}
else
{
lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; 
x_71 = lean_ctor_get(x_25, 0);
x_72 = lean_ctor_get_uint8(x_25, sizeof(void*)*3);
x_73 = lean_ctor_get(x_25, 1);
x_74 = lean_ctor_get(x_25, 2);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_71);
lean_dec(x_25);
x_75 = l_Lake_BuildTrace_mix(x_1, x_73);
x_76 = lean_apply_1(x_2, x_26);
x_77 = 1;
x_78 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_78, 0, x_71);
lean_ctor_set(x_78, 1, x_75);
lean_ctor_set(x_78, 2, x_74);
lean_ctor_set_uint8(x_78, sizeof(void*)*3, x_72);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_79 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_76, x_77, x_3, x_4, x_5, x_6, x_7, x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec_ref(x_79);
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_84 = lean_string_utf8_byte_size(x_82);
x_85 = lean_unsigned_to_nat(0u);
x_86 = lean_nat_dec_eq(x_84, x_85);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_87 = lean_ctor_get(x_81, 0);
lean_inc_ref(x_87);
x_88 = lean_ctor_get_uint8(x_81, sizeof(void*)*3);
x_89 = lean_ctor_get(x_81, 1);
lean_inc_ref(x_89);
x_90 = lean_ctor_get(x_81, 2);
lean_inc(x_90);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 lean_ctor_release(x_81, 2);
 x_91 = x_81;
} else {
 lean_dec_ref(x_81);
 x_91 = lean_box(0);
}
x_92 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_93 = l_Substring_takeWhileAux___at___Lake_inputBinFile_spec__6(x_82, x_84, x_85);
x_94 = l_Substring_takeRightWhileAux___at___Lake_inputBinFile_spec__7(x_82, x_93, x_84);
x_95 = lean_string_utf8_extract(x_82, x_93, x_94);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_82);
x_96 = lean_string_append(x_92, x_95);
lean_dec_ref(x_95);
x_97 = 1;
x_98 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set_uint8(x_98, sizeof(void*)*1, x_97);
x_99 = lean_box(0);
x_100 = lean_array_push(x_87, x_98);
if (lean_is_scalar(x_91)) {
 x_101 = lean_alloc_ctor(0, 3, 1);
} else {
 x_101 = x_91;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_89);
lean_ctor_set(x_101, 2, x_90);
lean_ctor_set_uint8(x_101, sizeof(void*)*3, x_88);
x_102 = l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__1(x_83, x_99, x_3, x_4, x_5, x_6, x_7, x_101);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_17 = x_102;
goto block_24;
}
else
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_84);
lean_dec(x_82);
x_103 = lean_box(0);
x_104 = l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__1(x_83, x_103, x_3, x_4, x_5, x_6, x_7, x_81);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_17 = x_104;
goto block_24;
}
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_105 = lean_ctor_get(x_79, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_79, 1);
lean_inc(x_106);
lean_dec_ref(x_79);
x_11 = x_105;
x_12 = x_106;
x_13 = lean_box(0);
goto block_16;
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_107 = !lean_is_exclusive(x_9);
if (x_107 == 0)
{
lean_object* x_108; 
x_108 = lean_task_pure(x_9);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_9, 0);
x_110 = lean_ctor_get(x_9, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_9);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_task_pure(x_111);
return x_112;
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_task_pure(x_14);
return x_15;
}
block_24:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_20);
lean_dec(x_18);
x_21 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__0), 2, 1);
lean_closure_set(x_21, 0, x_19);
x_22 = 1;
x_23 = lean_task_map(x_21, x_20, x_8, x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_dec(x_14);
lean_inc(x_3);
x_15 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__2___boxed), 10, 8);
lean_closure_set(x_15, 0, x_10);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_5);
lean_closure_set(x_15, 3, x_6);
lean_closure_set(x_15, 4, x_7);
lean_closure_set(x_15, 5, x_8);
lean_closure_set(x_15, 6, x_9);
lean_closure_set(x_15, 7, x_3);
x_16 = lean_io_bind_task(x_13, x_15, x_3, x_4);
x_17 = l_Lake_instDataKindDynlib;
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_16);
return x_1;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 2);
x_20 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
lean_inc(x_3);
x_21 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__2___boxed), 10, 8);
lean_closure_set(x_21, 0, x_10);
lean_closure_set(x_21, 1, x_2);
lean_closure_set(x_21, 2, x_5);
lean_closure_set(x_21, 3, x_6);
lean_closure_set(x_21, 4, x_7);
lean_closure_set(x_21, 5, x_8);
lean_closure_set(x_21, 6, x_9);
lean_closure_set(x_21, 7, x_3);
x_22 = lean_io_bind_task(x_18, x_21, x_3, x_4);
x_23 = l_Lake_instDataKindDynlib;
x_24 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_20);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(x_1, x_6);
x_17 = l_Array_append___redArg(x_16, x_2);
x_18 = l_Array_append___redArg(x_17, x_3);
x_19 = l_Lake_compileSharedLib(x_4, x_18, x_5, x_15);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 1);
lean_ctor_set(x_12, 0, x_21);
lean_ctor_set(x_19, 1, x_12);
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
lean_ctor_set(x_12, 0, x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_12);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_19, 1);
lean_ctor_set(x_12, 0, x_26);
lean_ctor_set(x_19, 1, x_12);
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
lean_ctor_set(x_12, 0, x_28);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_12);
return x_29;
}
}
}
else
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_12, 0);
x_31 = lean_ctor_get_uint8(x_12, sizeof(void*)*3);
x_32 = lean_ctor_get(x_12, 1);
x_33 = lean_ctor_get(x_12, 2);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_30);
lean_dec(x_12);
x_34 = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(x_1, x_6);
x_35 = l_Array_append___redArg(x_34, x_2);
x_36 = l_Array_append___redArg(x_35, x_3);
x_37 = l_Lake_compileSharedLib(x_4, x_36, x_5, x_30);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_32);
lean_ctor_set(x_41, 2, x_33);
lean_ctor_set_uint8(x_41, sizeof(void*)*3, x_31);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_45 = x_37;
} else {
 lean_dec_ref(x_37);
 x_45 = lean_box(0);
}
x_46 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_32);
lean_ctor_set(x_46, 2, x_33);
lean_ctor_set_uint8(x_46, sizeof(void*)*3, x_31);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (x_1 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_mk_empty_array_with_capacity(x_2);
x_13 = lean_apply_8(x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(x_4, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_apply_8(x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_16, lean_box(0));
return x_17;
}
else
{
uint8_t x_18; 
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
static lean_object* _init_l_Lake_buildSharedLib___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_sharedLibExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint64_t x_16; uint64_t x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_132 = l_Lake_platformTrace___closed__1;
x_133 = lean_unsigned_to_nat(0u);
x_134 = lean_array_get_size(x_1);
x_135 = lean_nat_dec_lt(x_133, x_134);
if (x_135 == 0)
{
lean_dec(x_134);
x_16 = x_132;
goto block_131;
}
else
{
uint8_t x_136; 
x_136 = lean_nat_dec_le(x_134, x_134);
if (x_136 == 0)
{
lean_dec(x_134);
x_16 = x_132;
goto block_131;
}
else
{
size_t x_137; size_t x_138; uint64_t x_139; 
x_137 = 0;
x_138 = lean_usize_of_nat(x_134);
lean_dec(x_134);
x_139 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_buildLeanO_spec__2(x_1, x_137, x_138, x_132);
x_16 = x_139;
goto block_131;
}
}
block_131:
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_18 = lean_ctor_get(x_14, 1);
x_19 = l_Lake_buildO___lam__2___closed__0;
x_20 = l_Lake_buildO___lam__2___closed__1;
x_21 = lean_array_to_list(x_1);
x_22 = l_List_toString___at___Lake_buildLeanO_spec__0(x_21);
lean_dec(x_21);
x_23 = lean_string_append(x_20, x_22);
lean_dec_ref(x_22);
x_24 = lean_string_append(x_19, x_23);
lean_dec_ref(x_23);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Lake_platformTrace___closed__4;
x_27 = l_Lake_platformTrace___closed__6;
x_28 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set_uint64(x_28, sizeof(void*)*3, x_16);
x_29 = l_Lake_BuildTrace_mix(x_18, x_28);
x_30 = l_Lake_platformTrace;
x_31 = l_Lake_BuildTrace_mix(x_29, x_30);
lean_ctor_set(x_14, 1, x_31);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_32 = lean_apply_7(x_2, x_9, x_10, x_11, x_12, x_13, x_14, lean_box(0));
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_33, 1);
x_37 = lean_box(x_3);
lean_inc_ref(x_8);
x_38 = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__1___boxed), 11, 4);
lean_closure_set(x_38, 0, x_37);
lean_closure_set(x_38, 1, x_25);
lean_closure_set(x_38, 2, x_4);
lean_closure_set(x_38, 3, x_8);
x_39 = l_Lake_BuildTrace_mix(x_36, x_34);
lean_ctor_set(x_33, 1, x_39);
x_40 = 1;
x_41 = 0;
x_42 = l_Lake_buildSharedLib___lam__2___closed__0;
x_43 = l_Lake_buildArtifactUnlessUpToDate(x_5, x_38, x_41, x_42, x_40, x_41, x_9, x_10, x_11, x_12, x_13, x_33);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_45, 1);
lean_inc_ref(x_46);
lean_dec(x_45);
x_47 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_6);
lean_ctor_set(x_47, 2, x_8);
lean_ctor_set_uint8(x_47, sizeof(void*)*3, x_7);
lean_ctor_set(x_43, 0, x_47);
return x_43;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_43, 0);
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_43);
x_50 = lean_ctor_get(x_48, 1);
lean_inc_ref(x_50);
lean_dec(x_48);
x_51 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_6);
lean_ctor_set(x_51, 2, x_8);
lean_ctor_set_uint8(x_51, sizeof(void*)*3, x_7);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_53 = !lean_is_exclusive(x_43);
if (x_53 == 0)
{
return x_43;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_43, 0);
x_55 = lean_ctor_get(x_43, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_43);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; 
x_57 = lean_ctor_get(x_33, 0);
x_58 = lean_ctor_get_uint8(x_33, sizeof(void*)*3);
x_59 = lean_ctor_get(x_33, 1);
x_60 = lean_ctor_get(x_33, 2);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_57);
lean_dec(x_33);
x_61 = lean_box(x_3);
lean_inc_ref(x_8);
x_62 = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__1___boxed), 11, 4);
lean_closure_set(x_62, 0, x_61);
lean_closure_set(x_62, 1, x_25);
lean_closure_set(x_62, 2, x_4);
lean_closure_set(x_62, 3, x_8);
x_63 = l_Lake_BuildTrace_mix(x_59, x_34);
x_64 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_64, 0, x_57);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_60);
lean_ctor_set_uint8(x_64, sizeof(void*)*3, x_58);
x_65 = 1;
x_66 = 0;
x_67 = l_Lake_buildSharedLib___lam__2___closed__0;
x_68 = l_Lake_buildArtifactUnlessUpToDate(x_5, x_62, x_66, x_67, x_65, x_66, x_9, x_10, x_11, x_12, x_13, x_64);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_71 = x_68;
} else {
 lean_dec_ref(x_68);
 x_71 = lean_box(0);
}
x_72 = lean_ctor_get(x_69, 1);
lean_inc_ref(x_72);
lean_dec(x_69);
x_73 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_6);
lean_ctor_set(x_73, 2, x_8);
lean_ctor_set_uint8(x_73, sizeof(void*)*3, x_7);
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_71;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_70);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_75 = lean_ctor_get(x_68, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_68, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_77 = x_68;
} else {
 lean_dec_ref(x_68);
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
uint8_t x_79; 
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_79 = !lean_is_exclusive(x_32);
if (x_79 == 0)
{
return x_32;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_32, 0);
x_81 = lean_ctor_get(x_32, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_32);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_83 = lean_ctor_get(x_14, 0);
x_84 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
x_85 = lean_ctor_get(x_14, 1);
x_86 = lean_ctor_get(x_14, 2);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_83);
lean_dec(x_14);
x_87 = l_Lake_buildO___lam__2___closed__0;
x_88 = l_Lake_buildO___lam__2___closed__1;
x_89 = lean_array_to_list(x_1);
x_90 = l_List_toString___at___Lake_buildLeanO_spec__0(x_89);
lean_dec(x_89);
x_91 = lean_string_append(x_88, x_90);
lean_dec_ref(x_90);
x_92 = lean_string_append(x_87, x_91);
lean_dec_ref(x_91);
x_93 = lean_unsigned_to_nat(0u);
x_94 = l_Lake_platformTrace___closed__4;
x_95 = l_Lake_platformTrace___closed__6;
x_96 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_96, 0, x_92);
lean_ctor_set(x_96, 1, x_94);
lean_ctor_set(x_96, 2, x_95);
lean_ctor_set_uint64(x_96, sizeof(void*)*3, x_16);
x_97 = l_Lake_BuildTrace_mix(x_85, x_96);
x_98 = l_Lake_platformTrace;
x_99 = l_Lake_BuildTrace_mix(x_97, x_98);
x_100 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_100, 0, x_83);
lean_ctor_set(x_100, 1, x_99);
lean_ctor_set(x_100, 2, x_86);
lean_ctor_set_uint8(x_100, sizeof(void*)*3, x_84);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_101 = lean_apply_7(x_2, x_9, x_10, x_11, x_12, x_13, x_100, lean_box(0));
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; 
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
lean_dec_ref(x_101);
x_104 = lean_ctor_get(x_102, 0);
lean_inc_ref(x_104);
x_105 = lean_ctor_get_uint8(x_102, sizeof(void*)*3);
x_106 = lean_ctor_get(x_102, 1);
lean_inc_ref(x_106);
x_107 = lean_ctor_get(x_102, 2);
lean_inc(x_107);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 lean_ctor_release(x_102, 2);
 x_108 = x_102;
} else {
 lean_dec_ref(x_102);
 x_108 = lean_box(0);
}
x_109 = lean_box(x_3);
lean_inc_ref(x_8);
x_110 = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__1___boxed), 11, 4);
lean_closure_set(x_110, 0, x_109);
lean_closure_set(x_110, 1, x_93);
lean_closure_set(x_110, 2, x_4);
lean_closure_set(x_110, 3, x_8);
x_111 = l_Lake_BuildTrace_mix(x_106, x_103);
if (lean_is_scalar(x_108)) {
 x_112 = lean_alloc_ctor(0, 3, 1);
} else {
 x_112 = x_108;
}
lean_ctor_set(x_112, 0, x_104);
lean_ctor_set(x_112, 1, x_111);
lean_ctor_set(x_112, 2, x_107);
lean_ctor_set_uint8(x_112, sizeof(void*)*3, x_105);
x_113 = 1;
x_114 = 0;
x_115 = l_Lake_buildSharedLib___lam__2___closed__0;
x_116 = l_Lake_buildArtifactUnlessUpToDate(x_5, x_110, x_114, x_115, x_113, x_114, x_9, x_10, x_11, x_12, x_13, x_112);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_119 = x_116;
} else {
 lean_dec_ref(x_116);
 x_119 = lean_box(0);
}
x_120 = lean_ctor_get(x_117, 1);
lean_inc_ref(x_120);
lean_dec(x_117);
x_121 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_6);
lean_ctor_set(x_121, 2, x_8);
lean_ctor_set_uint8(x_121, sizeof(void*)*3, x_7);
if (lean_is_scalar(x_119)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_119;
}
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_118);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_123 = lean_ctor_get(x_116, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_116, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_125 = x_116;
} else {
 lean_dec_ref(x_116);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_127 = lean_ctor_get(x_101, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_101, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_129 = x_101;
} else {
 lean_dec_ref(x_101);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(1, 2, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_128);
return x_130;
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
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_19 = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__0___boxed), 13, 5);
lean_closure_set(x_19, 0, x_10);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_2);
lean_closure_set(x_19, 3, x_3);
lean_closure_set(x_19, 4, x_4);
x_20 = lean_box(x_6);
x_21 = lean_box(x_8);
x_22 = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__2___boxed), 15, 7);
lean_closure_set(x_22, 0, x_2);
lean_closure_set(x_22, 1, x_5);
lean_closure_set(x_22, 2, x_20);
lean_closure_set(x_22, 3, x_19);
lean_closure_set(x_22, 4, x_3);
lean_closure_set(x_22, 5, x_7);
lean_closure_set(x_22, 6, x_21);
x_23 = l_Lake_buildSharedLib___lam__3___closed__0;
x_24 = l_Lake_Job_collectArray___redArg(x_9, x_23);
x_25 = lean_unsigned_to_nat(0u);
x_26 = 0;
lean_inc_ref(x_18);
x_27 = l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___redArg(x_24, x_22, x_25, x_26, x_11, x_12, x_13, x_14, x_15, x_18);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_16);
return x_28;
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
LEAN_EXPORT lean_object* l_Lake_buildSharedLib(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_18 = lean_box(x_10);
x_19 = lean_box(x_9);
x_20 = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__3___boxed), 17, 9);
lean_closure_set(x_20, 0, x_5);
lean_closure_set(x_20, 1, x_6);
lean_closure_set(x_20, 2, x_2);
lean_closure_set(x_20, 3, x_7);
lean_closure_set(x_20, 4, x_8);
lean_closure_set(x_20, 5, x_18);
lean_closure_set(x_20, 6, x_1);
lean_closure_set(x_20, 7, x_19);
lean_closure_set(x_20, 8, x_4);
x_21 = l_Lake_buildSharedLib___closed__0;
x_22 = l_Lake_Job_collectArray___redArg(x_3, x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = 1;
x_25 = l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg(x_22, x_20, x_23, x_24, x_11, x_12, x_13, x_14, x_15, x_16);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
x_13 = l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___redArg(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
x_14 = l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
x_13 = l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
x_14 = l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lake_buildSharedLib___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
x_13 = l_Lake_buildSharedLib___lam__1(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_3);
x_17 = lean_unbox(x_7);
x_18 = l_Lake_buildSharedLib___lam__2(x_1, x_2, x_16, x_4, x_5, x_6, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
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
x_19 = lean_unbox(x_8);
x_20 = l_Lake_buildSharedLib___lam__3(x_1, x_2, x_3, x_4, x_5, x_18, x_7, x_19, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec_ref(x_9);
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
x_19 = lean_unbox(x_10);
x_20 = l_Lake_buildSharedLib(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18, x_19, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec_ref(x_3);
return x_20;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLib___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1;
x_2 = l_Lake_buildLeanO___lam__0___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec_ref(x_11);
x_15 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_16);
lean_dec_ref(x_15);
if (x_5 == 0)
{
lean_object* x_66; 
x_66 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0;
x_17 = x_66;
x_18 = x_12;
x_19 = lean_box(0);
goto block_65;
}
else
{
lean_object* x_67; 
x_67 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(x_6, x_12);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec_ref(x_67);
x_17 = x_68;
x_18 = x_69;
x_19 = lean_box(0);
goto block_65;
}
else
{
uint8_t x_70; 
lean_dec_ref(x_16);
lean_dec_ref(x_4);
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
block_65:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_16, 3);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_16, 12);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_16, 18);
lean_inc_ref(x_22);
lean_dec_ref(x_16);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(x_1, x_17);
lean_dec_ref(x_17);
x_26 = l_Array_append___redArg(x_25, x_2);
x_27 = l_Array_append___redArg(x_26, x_3);
x_28 = l_Lake_buildLeanSharedLib___lam__0___closed__0;
x_29 = lean_array_push(x_28, x_20);
x_30 = l_Array_append___redArg(x_27, x_29);
lean_dec_ref(x_29);
x_31 = l_Array_append___redArg(x_30, x_22);
lean_dec_ref(x_22);
x_32 = l_Lake_compileSharedLib(x_4, x_31, x_21, x_24);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 1);
lean_ctor_set(x_18, 0, x_34);
lean_ctor_set(x_32, 1, x_18);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_32, 0);
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_32);
lean_ctor_set(x_18, 0, x_36);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_18);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_32);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_32, 1);
lean_ctor_set(x_18, 0, x_39);
lean_ctor_set(x_32, 1, x_18);
return x_32;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_32, 0);
x_41 = lean_ctor_get(x_32, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_32);
lean_ctor_set(x_18, 0, x_41);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_18);
return x_42;
}
}
}
else
{
lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_43 = lean_ctor_get(x_18, 0);
x_44 = lean_ctor_get_uint8(x_18, sizeof(void*)*3);
x_45 = lean_ctor_get(x_18, 1);
x_46 = lean_ctor_get(x_18, 2);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_43);
lean_dec(x_18);
x_47 = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(x_1, x_17);
lean_dec_ref(x_17);
x_48 = l_Array_append___redArg(x_47, x_2);
x_49 = l_Array_append___redArg(x_48, x_3);
x_50 = l_Lake_buildLeanSharedLib___lam__0___closed__0;
x_51 = lean_array_push(x_50, x_20);
x_52 = l_Array_append___redArg(x_49, x_51);
lean_dec_ref(x_51);
x_53 = l_Array_append___redArg(x_52, x_22);
lean_dec_ref(x_22);
x_54 = l_Lake_compileSharedLib(x_4, x_53, x_21, x_43);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
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
x_58 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_45);
lean_ctor_set(x_58, 2, x_46);
lean_ctor_set_uint8(x_58, sizeof(void*)*3, x_44);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_54, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_54, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_62 = x_54;
} else {
 lean_dec_ref(x_54);
 x_62 = lean_box(0);
}
x_63 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_45);
lean_ctor_set(x_63, 2, x_46);
lean_ctor_set_uint8(x_63, sizeof(void*)*3, x_44);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_60);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; uint64_t x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_16);
x_17 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
x_18 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_14, 2);
lean_inc(x_19);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_20 = x_14;
} else {
 lean_dec_ref(x_14);
 x_20 = lean_box(0);
}
x_21 = lean_ctor_get(x_13, 2);
x_22 = lean_box(x_5);
lean_inc_ref(x_8);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_23 = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__0___boxed), 13, 6);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_2);
lean_closure_set(x_23, 2, x_3);
lean_closure_set(x_23, 3, x_4);
lean_closure_set(x_23, 4, x_22);
lean_closure_set(x_23, 5, x_8);
lean_inc_ref(x_21);
x_24 = l_Lake_BuildTrace_mix(x_18, x_21);
x_57 = l_Lake_platformTrace___closed__1;
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_array_get_size(x_3);
x_60 = lean_nat_dec_lt(x_58, x_59);
if (x_60 == 0)
{
lean_dec(x_59);
x_25 = x_57;
goto block_56;
}
else
{
uint8_t x_61; 
x_61 = lean_nat_dec_le(x_59, x_59);
if (x_61 == 0)
{
lean_dec(x_59);
x_25 = x_57;
goto block_56;
}
else
{
size_t x_62; size_t x_63; uint64_t x_64; 
x_62 = 0;
x_63 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_64 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_buildLeanO_spec__2(x_3, x_62, x_63, x_57);
x_25 = x_64;
goto block_56;
}
}
block_56:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_26 = l_Lake_buildO___lam__2___closed__0;
x_27 = l_Lake_buildO___lam__2___closed__1;
x_28 = lean_array_to_list(x_3);
x_29 = l_List_toString___at___Lake_buildLeanO_spec__0(x_28);
lean_dec(x_28);
x_30 = lean_string_append(x_27, x_29);
lean_dec_ref(x_29);
x_31 = lean_string_append(x_26, x_30);
lean_dec_ref(x_30);
x_32 = l_Lake_platformTrace___closed__4;
x_33 = l_Lake_platformTrace___closed__6;
x_34 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set_uint64(x_34, sizeof(void*)*3, x_25);
x_35 = l_Lake_BuildTrace_mix(x_24, x_34);
x_36 = l_Lake_platformTrace;
x_37 = l_Lake_BuildTrace_mix(x_35, x_36);
if (lean_is_scalar(x_20)) {
 x_38 = lean_alloc_ctor(0, 3, 1);
} else {
 x_38 = x_20;
}
lean_ctor_set(x_38, 0, x_16);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_19);
lean_ctor_set_uint8(x_38, sizeof(void*)*3, x_17);
x_39 = 0;
x_40 = l_Lake_buildSharedLib___lam__2___closed__0;
x_41 = 1;
x_42 = l_Lake_buildArtifactUnlessUpToDate(x_4, x_23, x_39, x_40, x_41, x_39, x_9, x_10, x_11, x_12, x_13, x_38);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_44, 1);
lean_inc_ref(x_45);
lean_dec(x_44);
x_46 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_6);
lean_ctor_set(x_46, 2, x_8);
lean_ctor_set_uint8(x_46, sizeof(void*)*3, x_7);
lean_ctor_set(x_42, 0, x_46);
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_ctor_get(x_47, 1);
lean_inc_ref(x_49);
lean_dec(x_47);
x_50 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_6);
lean_ctor_set(x_50, 2, x_8);
lean_ctor_set_uint8(x_50, sizeof(void*)*3, x_7);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_52 = !lean_is_exclusive(x_42);
if (x_52 == 0)
{
return x_42;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_42, 0);
x_54 = lean_ctor_get(x_42, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_42);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_14, 1);
x_17 = lean_box(x_4);
x_18 = lean_box(x_6);
x_19 = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__1___boxed), 15, 7);
lean_closure_set(x_19, 0, x_8);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_2);
lean_closure_set(x_19, 3, x_3);
lean_closure_set(x_19, 4, x_17);
lean_closure_set(x_19, 5, x_5);
lean_closure_set(x_19, 6, x_18);
x_20 = l_Lake_buildSharedLib___lam__3___closed__0;
x_21 = l_Lake_Job_collectArray___redArg(x_7, x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = 0;
lean_inc_ref(x_16);
x_24 = l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___redArg(x_21, x_19, x_22, x_23, x_9, x_10, x_11, x_12, x_13, x_16);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_14);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_16 = lean_box(x_8);
x_17 = lean_box(x_7);
x_18 = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__2___boxed), 15, 7);
lean_closure_set(x_18, 0, x_5);
lean_closure_set(x_18, 1, x_6);
lean_closure_set(x_18, 2, x_2);
lean_closure_set(x_18, 3, x_16);
lean_closure_set(x_18, 4, x_1);
lean_closure_set(x_18, 5, x_17);
lean_closure_set(x_18, 6, x_4);
x_19 = l_Lake_buildSharedLib___closed__0;
x_20 = l_Lake_Job_collectArray___redArg(x_3, x_19);
x_21 = lean_unsigned_to_nat(0u);
x_22 = 1;
x_23 = l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg(x_20, x_18, x_21, x_22, x_9, x_10, x_11, x_12, x_13, x_14);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_5);
x_15 = l_Lake_buildLeanSharedLib___lam__0(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_5);
x_17 = lean_unbox(x_7);
x_18 = l_Lake_buildLeanSharedLib___lam__1(x_1, x_2, x_3, x_4, x_16, x_6, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_4);
x_17 = lean_unbox(x_6);
x_18 = l_Lake_buildLeanSharedLib___lam__2(x_1, x_2, x_3, x_16, x_5, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_7);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_7);
x_17 = lean_unbox(x_8);
x_18 = l_Lake_buildLeanSharedLib(x_1, x_2, x_3, x_4, x_5, x_6, x_16, x_17, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_3);
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
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_17; 
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_9, 0);
lean_inc(x_26);
lean_dec_ref(x_9);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_25, 1);
x_29 = l_Lake_BuildTrace_mix(x_1, x_28);
x_30 = lean_apply_1(x_2, x_26);
x_31 = 1;
lean_ctor_set(x_25, 1, x_29);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_32 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_30, x_31, x_3, x_4, x_5, x_6, x_7, x_25);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_string_utf8_byte_size(x_35);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_nat_dec_eq(x_37, x_38);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_34);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_41 = lean_ctor_get(x_34, 0);
x_42 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_43 = l_Substring_takeWhileAux___at___Lake_inputBinFile_spec__6(x_35, x_37, x_38);
x_44 = l_Substring_takeRightWhileAux___at___Lake_inputBinFile_spec__7(x_35, x_43, x_37);
x_45 = lean_string_utf8_extract(x_35, x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_35);
x_46 = lean_string_append(x_42, x_45);
lean_dec_ref(x_45);
x_47 = 1;
x_48 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_47);
x_49 = lean_box(0);
x_50 = lean_array_push(x_41, x_48);
lean_ctor_set(x_34, 0, x_50);
x_51 = l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__1(x_36, x_49, x_3, x_4, x_5, x_6, x_7, x_34);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_17 = x_51;
goto block_24;
}
else
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_52 = lean_ctor_get(x_34, 0);
x_53 = lean_ctor_get_uint8(x_34, sizeof(void*)*3);
x_54 = lean_ctor_get(x_34, 1);
x_55 = lean_ctor_get(x_34, 2);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_52);
lean_dec(x_34);
x_56 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_57 = l_Substring_takeWhileAux___at___Lake_inputBinFile_spec__6(x_35, x_37, x_38);
x_58 = l_Substring_takeRightWhileAux___at___Lake_inputBinFile_spec__7(x_35, x_57, x_37);
x_59 = lean_string_utf8_extract(x_35, x_57, x_58);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_35);
x_60 = lean_string_append(x_56, x_59);
lean_dec_ref(x_59);
x_61 = 1;
x_62 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_61);
x_63 = lean_box(0);
x_64 = lean_array_push(x_52, x_62);
x_65 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_54);
lean_ctor_set(x_65, 2, x_55);
lean_ctor_set_uint8(x_65, sizeof(void*)*3, x_53);
x_66 = l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__1(x_36, x_63, x_3, x_4, x_5, x_6, x_7, x_65);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_17 = x_66;
goto block_24;
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_37);
lean_dec(x_35);
x_67 = lean_box(0);
x_68 = l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__1(x_36, x_67, x_3, x_4, x_5, x_6, x_7, x_34);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_17 = x_68;
goto block_24;
}
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_69 = lean_ctor_get(x_32, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_32, 1);
lean_inc(x_70);
lean_dec_ref(x_32);
x_11 = x_69;
x_12 = x_70;
x_13 = lean_box(0);
goto block_16;
}
}
else
{
lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; 
x_71 = lean_ctor_get(x_25, 0);
x_72 = lean_ctor_get_uint8(x_25, sizeof(void*)*3);
x_73 = lean_ctor_get(x_25, 1);
x_74 = lean_ctor_get(x_25, 2);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_71);
lean_dec(x_25);
x_75 = l_Lake_BuildTrace_mix(x_1, x_73);
x_76 = lean_apply_1(x_2, x_26);
x_77 = 1;
x_78 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_78, 0, x_71);
lean_ctor_set(x_78, 1, x_75);
lean_ctor_set(x_78, 2, x_74);
lean_ctor_set_uint8(x_78, sizeof(void*)*3, x_72);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_79 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_76, x_77, x_3, x_4, x_5, x_6, x_7, x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec_ref(x_79);
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_84 = lean_string_utf8_byte_size(x_82);
x_85 = lean_unsigned_to_nat(0u);
x_86 = lean_nat_dec_eq(x_84, x_85);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_87 = lean_ctor_get(x_81, 0);
lean_inc_ref(x_87);
x_88 = lean_ctor_get_uint8(x_81, sizeof(void*)*3);
x_89 = lean_ctor_get(x_81, 1);
lean_inc_ref(x_89);
x_90 = lean_ctor_get(x_81, 2);
lean_inc(x_90);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 lean_ctor_release(x_81, 2);
 x_91 = x_81;
} else {
 lean_dec_ref(x_81);
 x_91 = lean_box(0);
}
x_92 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_93 = l_Substring_takeWhileAux___at___Lake_inputBinFile_spec__6(x_82, x_84, x_85);
x_94 = l_Substring_takeRightWhileAux___at___Lake_inputBinFile_spec__7(x_82, x_93, x_84);
x_95 = lean_string_utf8_extract(x_82, x_93, x_94);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_82);
x_96 = lean_string_append(x_92, x_95);
lean_dec_ref(x_95);
x_97 = 1;
x_98 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set_uint8(x_98, sizeof(void*)*1, x_97);
x_99 = lean_box(0);
x_100 = lean_array_push(x_87, x_98);
if (lean_is_scalar(x_91)) {
 x_101 = lean_alloc_ctor(0, 3, 1);
} else {
 x_101 = x_91;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_89);
lean_ctor_set(x_101, 2, x_90);
lean_ctor_set_uint8(x_101, sizeof(void*)*3, x_88);
x_102 = l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__1(x_83, x_99, x_3, x_4, x_5, x_6, x_7, x_101);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_17 = x_102;
goto block_24;
}
else
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_84);
lean_dec(x_82);
x_103 = lean_box(0);
x_104 = l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__1(x_83, x_103, x_3, x_4, x_5, x_6, x_7, x_81);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_17 = x_104;
goto block_24;
}
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_105 = lean_ctor_get(x_79, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_79, 1);
lean_inc(x_106);
lean_dec_ref(x_79);
x_11 = x_105;
x_12 = x_106;
x_13 = lean_box(0);
goto block_16;
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_107 = !lean_is_exclusive(x_9);
if (x_107 == 0)
{
lean_object* x_108; 
x_108 = lean_task_pure(x_9);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_9, 0);
x_110 = lean_ctor_get(x_9, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_9);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_task_pure(x_111);
return x_112;
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_task_pure(x_14);
return x_15;
}
block_24:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_20);
lean_dec(x_18);
x_21 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(x_21, 0, x_19);
x_22 = 1;
x_23 = lean_task_map(x_21, x_20, x_8, x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_dec(x_14);
lean_inc(x_3);
x_15 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__2___boxed), 10, 8);
lean_closure_set(x_15, 0, x_10);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_5);
lean_closure_set(x_15, 3, x_6);
lean_closure_set(x_15, 4, x_7);
lean_closure_set(x_15, 5, x_8);
lean_closure_set(x_15, 6, x_9);
lean_closure_set(x_15, 7, x_3);
x_16 = lean_io_bind_task(x_13, x_15, x_3, x_4);
x_17 = l_Lake_instDataKindFilePath;
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_16);
return x_1;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 2);
x_20 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
lean_inc(x_3);
x_21 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__2___boxed), 10, 8);
lean_closure_set(x_21, 0, x_10);
lean_closure_set(x_21, 1, x_2);
lean_closure_set(x_21, 2, x_5);
lean_closure_set(x_21, 3, x_6);
lean_closure_set(x_21, 4, x_7);
lean_closure_set(x_21, 5, x_8);
lean_closure_set(x_21, 6, x_9);
lean_closure_set(x_21, 7, x_3);
x_22 = lean_io_bind_task(x_18, x_21, x_3, x_4);
x_23 = l_Lake_instDataKindFilePath;
x_24 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_20);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(x_1, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec_ref(x_11);
x_16 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_17);
lean_dec_ref(x_16);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec_ref(x_14);
x_20 = lean_ctor_get(x_17, 3);
x_21 = lean_ctor_get(x_17, 12);
lean_inc_ref(x_21);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(x_2, x_19);
lean_dec(x_19);
x_25 = l_Array_append___redArg(x_24, x_3);
x_26 = l_Array_append___redArg(x_25, x_4);
x_27 = l_Lake_buildLeanSharedLib___lam__0___closed__0;
lean_inc_ref(x_20);
x_28 = lean_array_push(x_27, x_20);
x_29 = l_Array_append___redArg(x_26, x_28);
lean_dec_ref(x_28);
x_30 = l_Lake_LeanInstall_ccLinkFlags(x_5, x_17);
lean_dec_ref(x_17);
x_31 = l_Array_append___redArg(x_29, x_30);
lean_dec_ref(x_30);
x_32 = l_Lake_compileExe(x_6, x_31, x_21, x_23);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 1);
lean_ctor_set(x_18, 0, x_34);
lean_ctor_set(x_32, 1, x_18);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_32, 0);
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_32);
lean_ctor_set(x_18, 0, x_36);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_18);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_32);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_32, 1);
lean_ctor_set(x_18, 0, x_39);
lean_ctor_set(x_32, 1, x_18);
return x_32;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_32, 0);
x_41 = lean_ctor_get(x_32, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_32);
lean_ctor_set(x_18, 0, x_41);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_18);
return x_42;
}
}
}
else
{
lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_43 = lean_ctor_get(x_18, 0);
x_44 = lean_ctor_get_uint8(x_18, sizeof(void*)*3);
x_45 = lean_ctor_get(x_18, 1);
x_46 = lean_ctor_get(x_18, 2);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_43);
lean_dec(x_18);
x_47 = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(x_2, x_19);
lean_dec(x_19);
x_48 = l_Array_append___redArg(x_47, x_3);
x_49 = l_Array_append___redArg(x_48, x_4);
x_50 = l_Lake_buildLeanSharedLib___lam__0___closed__0;
lean_inc_ref(x_20);
x_51 = lean_array_push(x_50, x_20);
x_52 = l_Array_append___redArg(x_49, x_51);
lean_dec_ref(x_51);
x_53 = l_Lake_LeanInstall_ccLinkFlags(x_5, x_17);
lean_dec_ref(x_17);
x_54 = l_Array_append___redArg(x_52, x_53);
lean_dec_ref(x_53);
x_55 = l_Lake_compileExe(x_6, x_54, x_21, x_43);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
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
x_59 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_45);
lean_ctor_set(x_59, 2, x_46);
lean_ctor_set_uint8(x_59, sizeof(void*)*3, x_44);
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_56);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_55, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_63 = x_55;
} else {
 lean_dec_ref(x_55);
 x_63 = lean_box(0);
}
x_64 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_45);
lean_ctor_set(x_64, 2, x_46);
lean_ctor_set_uint8(x_64, sizeof(void*)*3, x_44);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_61);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec_ref(x_11);
lean_dec_ref(x_6);
x_66 = !lean_is_exclusive(x_14);
if (x_66 == 0)
{
return x_14;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_14, 0);
x_68 = lean_ctor_get(x_14, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_14);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
static lean_object* _init_l_Lake_buildLeanExe___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_System_FilePath_exeExtension;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; uint64_t x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_14);
x_15 = lean_ctor_get_uint8(x_12, sizeof(void*)*3);
x_16 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_12, 2);
lean_inc(x_17);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 x_18 = x_12;
} else {
 lean_dec_ref(x_12);
 x_18 = lean_box(0);
}
x_19 = lean_ctor_get(x_11, 2);
x_20 = lean_box(x_4);
lean_inc_ref(x_5);
lean_inc_ref(x_3);
x_21 = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__0___boxed), 13, 6);
lean_closure_set(x_21, 0, x_6);
lean_closure_set(x_21, 1, x_1);
lean_closure_set(x_21, 2, x_2);
lean_closure_set(x_21, 3, x_3);
lean_closure_set(x_21, 4, x_20);
lean_closure_set(x_21, 5, x_5);
lean_inc_ref(x_19);
x_22 = l_Lake_BuildTrace_mix(x_16, x_19);
x_53 = l_Lake_platformTrace___closed__1;
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_array_get_size(x_3);
x_56 = lean_nat_dec_lt(x_54, x_55);
if (x_56 == 0)
{
lean_dec(x_55);
x_23 = x_53;
goto block_52;
}
else
{
uint8_t x_57; 
x_57 = lean_nat_dec_le(x_55, x_55);
if (x_57 == 0)
{
lean_dec(x_55);
x_23 = x_53;
goto block_52;
}
else
{
size_t x_58; size_t x_59; uint64_t x_60; 
x_58 = 0;
x_59 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_60 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_buildLeanO_spec__2(x_3, x_58, x_59, x_53);
x_23 = x_60;
goto block_52;
}
}
block_52:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_24 = l_Lake_buildO___lam__2___closed__0;
x_25 = l_Lake_buildO___lam__2___closed__1;
x_26 = lean_array_to_list(x_3);
x_27 = l_List_toString___at___Lake_buildLeanO_spec__0(x_26);
lean_dec(x_26);
x_28 = lean_string_append(x_25, x_27);
lean_dec_ref(x_27);
x_29 = lean_string_append(x_24, x_28);
lean_dec_ref(x_28);
x_30 = l_Lake_platformTrace___closed__4;
x_31 = l_Lake_platformTrace___closed__6;
x_32 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_31);
lean_ctor_set_uint64(x_32, sizeof(void*)*3, x_23);
x_33 = l_Lake_BuildTrace_mix(x_22, x_32);
x_34 = l_Lake_platformTrace;
x_35 = l_Lake_BuildTrace_mix(x_33, x_34);
if (lean_is_scalar(x_18)) {
 x_36 = lean_alloc_ctor(0, 3, 1);
} else {
 x_36 = x_18;
}
lean_ctor_set(x_36, 0, x_14);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_17);
lean_ctor_set_uint8(x_36, sizeof(void*)*3, x_15);
x_37 = 0;
x_38 = l_Lake_buildLeanExe___lam__1___closed__0;
x_39 = 1;
x_40 = l_Lake_buildArtifactUnlessUpToDate(x_5, x_21, x_37, x_38, x_39, x_39, x_7, x_8, x_9, x_10, x_11, x_36);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_42, 1);
lean_inc_ref(x_43);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_43);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_40, 0);
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_40);
x_46 = lean_ctor_get(x_44, 1);
lean_inc_ref(x_46);
lean_dec(x_44);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_40);
if (x_48 == 0)
{
return x_40;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_40, 0);
x_50 = lean_ctor_get(x_40, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_40);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_12, 1);
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
x_20 = 0;
lean_inc_ref(x_14);
x_21 = l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3___redArg(x_18, x_16, x_19, x_20, x_7, x_8, x_9, x_10, x_11, x_14);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_12);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
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
x_19 = 1;
x_20 = l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg(x_17, x_15, x_18, x_19, x_7, x_8, x_9, x_10, x_11, x_12);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
x_13 = l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
x_14 = l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_5);
x_15 = l_Lake_buildLeanExe___lam__0(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
x_15 = l_Lake_buildLeanExe___lam__1(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
x_15 = l_Lake_buildLeanExe___lam__2(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_6);
x_15 = l_Lake_buildLeanExe(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_2);
return x_15;
}
}
lean_object* initialize_Lake_Build_Job_Monad(uint8_t builtin);
lean_object* initialize_Lake_Config_Monad(uint8_t builtin);
lean_object* initialize_Lake_Util_JsonObject(uint8_t builtin);
lean_object* initialize_Lake_Util_IO(uint8_t builtin);
lean_object* initialize_Lake_Build_Target_Fetch(uint8_t builtin);
lean_object* initialize_Lake_Build_Actions(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Common(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Job_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_JsonObject(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Target_Fetch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Actions(builtin);
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
l_Lake_platformTrace___closed__0 = _init_l_Lake_platformTrace___closed__0();
lean_mark_persistent(l_Lake_platformTrace___closed__0);
l_Lake_platformTrace___closed__1 = _init_l_Lake_platformTrace___closed__1();
l_Lake_platformTrace___closed__2 = _init_l_Lake_platformTrace___closed__2();
l_Lake_platformTrace___closed__3 = _init_l_Lake_platformTrace___closed__3();
l_Lake_platformTrace___closed__4 = _init_l_Lake_platformTrace___closed__4();
lean_mark_persistent(l_Lake_platformTrace___closed__4);
l_Lake_platformTrace___closed__5 = _init_l_Lake_platformTrace___closed__5();
lean_mark_persistent(l_Lake_platformTrace___closed__5);
l_Lake_platformTrace___closed__6 = _init_l_Lake_platformTrace___closed__6();
lean_mark_persistent(l_Lake_platformTrace___closed__6);
l_Lake_platformTrace___closed__7 = _init_l_Lake_platformTrace___closed__7();
lean_mark_persistent(l_Lake_platformTrace___closed__7);
l_Lake_platformTrace = _init_l_Lake_platformTrace();
lean_mark_persistent(l_Lake_platformTrace);
l_Lake_addPureTrace___redArg___closed__0 = _init_l_Lake_addPureTrace___redArg___closed__0();
lean_mark_persistent(l_Lake_addPureTrace___redArg___closed__0);
l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0 = _init_l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0);
l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion = _init_l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion);
l_Prod_toJson___at___Array_toJson___at___Lake_BuildMetadata_toJson_spec__0_spec__0___closed__0 = _init_l_Prod_toJson___at___Array_toJson___at___Lake_BuildMetadata_toJson_spec__0_spec__0___closed__0();
lean_mark_persistent(l_Prod_toJson___at___Array_toJson___at___Lake_BuildMetadata_toJson_spec__0_spec__0___closed__0);
l_Lake_BuildMetadata_toJson___closed__0 = _init_l_Lake_BuildMetadata_toJson___closed__0();
lean_mark_persistent(l_Lake_BuildMetadata_toJson___closed__0);
l_Lake_BuildMetadata_toJson___closed__1 = _init_l_Lake_BuildMetadata_toJson___closed__1();
lean_mark_persistent(l_Lake_BuildMetadata_toJson___closed__1);
l_Lake_BuildMetadata_toJson___closed__2 = _init_l_Lake_BuildMetadata_toJson___closed__2();
lean_mark_persistent(l_Lake_BuildMetadata_toJson___closed__2);
l_Lake_BuildMetadata_toJson___closed__3 = _init_l_Lake_BuildMetadata_toJson___closed__3();
lean_mark_persistent(l_Lake_BuildMetadata_toJson___closed__3);
l_Lake_BuildMetadata_toJson___closed__4 = _init_l_Lake_BuildMetadata_toJson___closed__4();
lean_mark_persistent(l_Lake_BuildMetadata_toJson___closed__4);
l_Lake_BuildMetadata_toJson___closed__5 = _init_l_Lake_BuildMetadata_toJson___closed__5();
lean_mark_persistent(l_Lake_BuildMetadata_toJson___closed__5);
l_Lake_BuildMetadata_toJson___closed__6 = _init_l_Lake_BuildMetadata_toJson___closed__6();
lean_mark_persistent(l_Lake_BuildMetadata_toJson___closed__6);
l_Lake_BuildMetadata_toJson___closed__7 = _init_l_Lake_BuildMetadata_toJson___closed__7();
lean_mark_persistent(l_Lake_BuildMetadata_toJson___closed__7);
l_Lake_instToJsonBuildMetadata___closed__0 = _init_l_Lake_instToJsonBuildMetadata___closed__0();
lean_mark_persistent(l_Lake_instToJsonBuildMetadata___closed__0);
l_Lake_instToJsonBuildMetadata = _init_l_Lake_instToJsonBuildMetadata();
lean_mark_persistent(l_Lake_instToJsonBuildMetadata);
l_Lake_BuildMetadata_ofStub___closed__0 = _init_l_Lake_BuildMetadata_ofStub___closed__0();
lean_mark_persistent(l_Lake_BuildMetadata_ofStub___closed__0);
l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__0___closed__0 = _init_l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__0___closed__0();
lean_mark_persistent(l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__0___closed__0);
l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__0 = _init_l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__0();
lean_mark_persistent(l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__0);
l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1 = _init_l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1();
lean_mark_persistent(l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1);
l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__1___closed__0 = _init_l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__1___closed__0();
lean_mark_persistent(l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__1___closed__0);
l_Option_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__4_spec__4___closed__0 = _init_l_Option_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__4_spec__4___closed__0();
lean_mark_persistent(l_Option_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__4_spec__4___closed__0);
l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__4___closed__0 = _init_l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__4___closed__0();
lean_mark_persistent(l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__4___closed__0);
l_Prod_fromJson_x3f___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__6_spec__6_spec__6___closed__0 = _init_l_Prod_fromJson_x3f___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__6_spec__6_spec__6___closed__0();
lean_mark_persistent(l_Prod_fromJson_x3f___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__6_spec__6_spec__6___closed__0);
l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__6___closed__0 = _init_l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__6___closed__0();
lean_mark_persistent(l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJsonObject_x3f_spec__6___closed__0);
l_Lake_BuildMetadata_fromJsonObject_x3f___closed__0 = _init_l_Lake_BuildMetadata_fromJsonObject_x3f___closed__0();
lean_mark_persistent(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__0);
l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1 = _init_l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1();
lean_mark_persistent(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1);
l_Lake_BuildMetadata_fromJsonObject_x3f___closed__2 = _init_l_Lake_BuildMetadata_fromJsonObject_x3f___closed__2();
lean_mark_persistent(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__2);
l_Lake_BuildMetadata_fromJsonObject_x3f___closed__3 = _init_l_Lake_BuildMetadata_fromJsonObject_x3f___closed__3();
lean_mark_persistent(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__3);
l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4 = _init_l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4();
lean_mark_persistent(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4);
l_Lake_BuildMetadata_fromJsonObject_x3f___closed__5 = _init_l_Lake_BuildMetadata_fromJsonObject_x3f___closed__5();
lean_mark_persistent(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__5);
l_Lake_BuildMetadata_fromJsonObject_x3f___closed__6 = _init_l_Lake_BuildMetadata_fromJsonObject_x3f___closed__6();
lean_mark_persistent(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__6);
l_Lake_BuildMetadata_fromJsonObject_x3f___closed__7 = _init_l_Lake_BuildMetadata_fromJsonObject_x3f___closed__7();
lean_mark_persistent(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__7);
l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8 = _init_l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8();
lean_mark_persistent(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8);
l_Lake_BuildMetadata_fromJsonObject_x3f___closed__9 = _init_l_Lake_BuildMetadata_fromJsonObject_x3f___closed__9();
lean_mark_persistent(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__9);
l_Lake_BuildMetadata_fromJsonObject_x3f___closed__10 = _init_l_Lake_BuildMetadata_fromJsonObject_x3f___closed__10();
lean_mark_persistent(l_Lake_BuildMetadata_fromJsonObject_x3f___closed__10);
l_Lake_BuildMetadata_fromJson_x3f___lam__0___closed__0 = _init_l_Lake_BuildMetadata_fromJson_x3f___lam__0___closed__0();
lean_mark_persistent(l_Lake_BuildMetadata_fromJson_x3f___lam__0___closed__0);
l_Lake_BuildMetadata_fromJson_x3f___closed__0 = _init_l_Lake_BuildMetadata_fromJson_x3f___closed__0();
lean_mark_persistent(l_Lake_BuildMetadata_fromJson_x3f___closed__0);
l_Lake_BuildMetadata_fromJson_x3f___closed__1 = _init_l_Lake_BuildMetadata_fromJson_x3f___closed__1();
lean_mark_persistent(l_Lake_BuildMetadata_fromJson_x3f___closed__1);
l_Lake_BuildMetadata_fromJson_x3f___closed__2 = _init_l_Lake_BuildMetadata_fromJson_x3f___closed__2();
lean_mark_persistent(l_Lake_BuildMetadata_fromJson_x3f___closed__2);
l_Lake_BuildMetadata_fromJson_x3f___closed__3 = _init_l_Lake_BuildMetadata_fromJson_x3f___closed__3();
lean_mark_persistent(l_Lake_BuildMetadata_fromJson_x3f___closed__3);
l_Lake_instFromJsonBuildMetadata___closed__0 = _init_l_Lake_instFromJsonBuildMetadata___closed__0();
lean_mark_persistent(l_Lake_instFromJsonBuildMetadata___closed__0);
l_Lake_instFromJsonBuildMetadata = _init_l_Lake_instFromJsonBuildMetadata();
lean_mark_persistent(l_Lake_instFromJsonBuildMetadata);
l_Lake_readTraceFile___closed__0 = _init_l_Lake_readTraceFile___closed__0();
lean_mark_persistent(l_Lake_readTraceFile___closed__0);
l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0 = _init_l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0);
l_Lake_instToOutputJsonPUnit = _init_l_Lake_instToOutputJsonPUnit();
lean_mark_persistent(l_Lake_instToOutputJsonPUnit);
l_Lake_instToOutputJsonArtifact___lam__0___closed__0 = _init_l_Lake_instToOutputJsonArtifact___lam__0___closed__0();
lean_mark_persistent(l_Lake_instToOutputJsonArtifact___lam__0___closed__0);
l_Lake_instToOutputJsonArtifact = _init_l_Lake_instToOutputJsonArtifact();
lean_mark_persistent(l_Lake_instToOutputJsonArtifact);
l_Lake_buildAction___redArg___closed__0 = _init_l_Lake_buildAction___redArg___closed__0();
lean_mark_persistent(l_Lake_buildAction___redArg___closed__0);
l_Lake_buildAction___redArg___closed__1 = _init_l_Lake_buildAction___redArg___closed__1();
lean_mark_persistent(l_Lake_buildAction___redArg___closed__1);
l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0 = _init_l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0();
lean_mark_persistent(l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0);
l_Lake_writeFileHash___closed__0 = _init_l_Lake_writeFileHash___closed__0();
lean_mark_persistent(l_Lake_writeFileHash___closed__0);
l_Lake_buildFileUnlessUpToDate_x27___closed__0 = _init_l_Lake_buildFileUnlessUpToDate_x27___closed__0();
lean_mark_persistent(l_Lake_buildFileUnlessUpToDate_x27___closed__0);
l_Lake_Cache_saveArtifact___closed__0 = _init_l_Lake_Cache_saveArtifact___closed__0();
lean_mark_persistent(l_Lake_Cache_saveArtifact___closed__0);
l_Lake_Cache_saveArtifact___closed__1 = _init_l_Lake_Cache_saveArtifact___closed__1();
lean_mark_persistent(l_Lake_Cache_saveArtifact___closed__1);
l_Lake_Cache_saveArtifact___closed__2 = _init_l_Lake_Cache_saveArtifact___closed__2();
lean_mark_persistent(l_Lake_Cache_saveArtifact___closed__2);
l_Lake_getArtifacts_x3f___redArg___closed__0 = _init_l_Lake_getArtifacts_x3f___redArg___closed__0();
lean_mark_persistent(l_Lake_getArtifacts_x3f___redArg___closed__0);
l_Lake_getArtifacts_x3f___redArg___closed__1 = _init_l_Lake_getArtifacts_x3f___redArg___closed__1();
lean_mark_persistent(l_Lake_getArtifacts_x3f___redArg___closed__1);
l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__0 = _init_l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__0();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__0);
l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__1 = _init_l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__1();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__1);
l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__2 = _init_l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__2();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__2);
l_Lake_buildArtifactUnlessUpToDate___lam__1___closed__0 = _init_l_Lake_buildArtifactUnlessUpToDate___lam__1___closed__0();
lean_mark_persistent(l_Lake_buildArtifactUnlessUpToDate___lam__1___closed__0);
l_Lake_buildFileAfterDep___redArg___lam__0___closed__0 = _init_l_Lake_buildFileAfterDep___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lake_buildFileAfterDep___redArg___lam__0___closed__0);
l_panic___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__3___closed__0 = _init_l_panic___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__3___closed__0();
lean_mark_persistent(l_panic___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__3___closed__0);
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
l_Lake_inputDir___lam__1___closed__0 = _init_l_Lake_inputDir___lam__1___closed__0();
lean_mark_persistent(l_Lake_inputDir___lam__1___closed__0);
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
l_List_foldl___at___List_toString___at___Lake_buildLeanO_spec__0_spec__0___closed__0 = _init_l_List_foldl___at___List_toString___at___Lake_buildLeanO_spec__0_spec__0___closed__0();
lean_mark_persistent(l_List_foldl___at___List_toString___at___Lake_buildLeanO_spec__0_spec__0___closed__0);
l_List_toString___at___Lake_buildLeanO_spec__0___closed__0 = _init_l_List_toString___at___Lake_buildLeanO_spec__0___closed__0();
lean_mark_persistent(l_List_toString___at___Lake_buildLeanO_spec__0___closed__0);
l_List_toString___at___Lake_buildLeanO_spec__0___closed__1 = _init_l_List_toString___at___Lake_buildLeanO_spec__0___closed__1();
lean_mark_persistent(l_List_toString___at___Lake_buildLeanO_spec__0___closed__1);
l_List_toString___at___Lake_buildLeanO_spec__0___closed__2 = _init_l_List_toString___at___Lake_buildLeanO_spec__0___closed__2();
lean_mark_persistent(l_List_toString___at___Lake_buildLeanO_spec__0___closed__2);
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
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1);
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
l_Lake_buildSharedLib___lam__2___closed__0 = _init_l_Lake_buildSharedLib___lam__2___closed__0();
lean_mark_persistent(l_Lake_buildSharedLib___lam__2___closed__0);
l_Lake_buildSharedLib___lam__3___closed__0 = _init_l_Lake_buildSharedLib___lam__3___closed__0();
lean_mark_persistent(l_Lake_buildSharedLib___lam__3___closed__0);
l_Lake_buildSharedLib___closed__0 = _init_l_Lake_buildSharedLib___closed__0();
lean_mark_persistent(l_Lake_buildSharedLib___closed__0);
l_Lake_buildLeanSharedLib___lam__0___closed__0 = _init_l_Lake_buildLeanSharedLib___lam__0___closed__0();
lean_mark_persistent(l_Lake_buildLeanSharedLib___lam__0___closed__0);
l_Lake_buildLeanExe___lam__1___closed__0 = _init_l_Lake_buildLeanExe___lam__1___closed__0();
lean_mark_persistent(l_Lake_buildLeanExe___lam__1___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

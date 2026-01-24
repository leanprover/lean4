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
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_invalid_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_read(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(lean_object*, lean_object*);
lean_object* l_Lake_compileO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonArtifact___lam__0(lean_object*);
static lean_object* l_Lake_buildO___closed__0;
static lean_object* l_Lake_buildO___lam__2___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t);
static lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__5;
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildSharedLib___lam__3___closed__0;
LEAN_EXPORT lean_object* l_Lake_writeFileHash(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instFromJsonBuildMetadata___closed__0;
lean_object* l_Lake_instMonadLiftLakeMBuildTOfPure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_toJson___closed__7;
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1___boxed(lean_object*);
static lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs___boxed(lean_object*, lean_object*);
lean_object* l_System_FilePath_walkDir(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildFileAfterDep___redArg___lam__0___closed__0;
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileHash(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ok_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addLeanTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0___closed__0;
static lean_object* l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3___closed__0;
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0(lean_object*);
static lean_object* l_Lake_instToOutputJsonPUnit___closed__0;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_mapM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instToOutputJsonArtifact___closed__0;
uint8_t l_Array_isEmpty___redArg(lean_object*);
lean_object* l_Lake_Cache_getArtifact___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildStaticLib___closed__0;
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_writeFile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__10;
lean_object* l_Lake_compileSharedLib(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_byte_array_hash(lean_object*);
uint8_t l_Lake_Workspace_enableArtifactCache(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2(lean_object*);
lean_object* l_Lake_JsonObject_insertJson(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4;
static lean_object* l_Lake_buildLeanO___lam__0___closed__1;
static lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__10;
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lake_computeTextFileHash(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate(uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_JsonObject_getJson_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__14;
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__3;
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_metadata(lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Hash_ofDecimal_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPureTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofHashCheck(uint8_t);
static lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__6;
static uint64_t l_Lake_platformTrace___closed__1;
lean_object* l_instMonadST(lean_object*);
extern lean_object* l_System_FilePath_exeExtension;
lean_object* l_Lake_Cache_writeOutputsCore(lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_platformTrace___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lake_EStateT_instPure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_bindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0;
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1(lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0___closed__0;
lean_object* l_instMonadST___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_ofStub___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_JobM_runFetchM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Cache_getArtifact(lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__1;
static lean_object* l_Lake_getArtifacts_x3f___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_CacheMap_insertCore(uint64_t, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheEnabled___at___00Lake_buildArtifactUnlessUpToDate_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
static lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg___closed__0;
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
lean_object* l_Lake_Dynlib_dir_x3f(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheEnabled___at___00Lake_buildArtifactUnlessUpToDate_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildTrace_mix(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2(lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_compileExe(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_sharedLibExt;
LEAN_EXPORT lean_object* l_Lake_addPureTrace___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EIO_toBaseIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_toJson___closed__3;
static lean_object* l_Lake_readTraceFile___closed__0;
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_platformTrace;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lake_instToOutputJsonArtifact___lam__0___closed__0;
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__2;
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_writeFileHash___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofHashCheck___boxed(lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now();
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___redArg(lean_object*, lean_object*);
lean_object* l_Lake_createParentDirs(lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableEqOutputStatus(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instFunctor___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_System_FilePath_isDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceJobM;
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(lean_object*);
static lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1;
static lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__0;
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__11;
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__8;
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_parse(lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildAction___redArg___closed__1;
static lean_object* l_Lake_cacheArtifact___redArg___closed__0;
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__12;
static lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3___closed__0;
LEAN_EXPORT lean_object* l_Lake_readTraceFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion;
static lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2___closed__0;
lean_object* l_Lake_Package_isArtifactCacheEnabled___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__1;
static lean_object* l_Lake_BuildMetadata_toJson___closed__1;
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFromJsonBuildMetadata;
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instAlternativeOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lake_removeFileIfExists(lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0(lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0;
static uint64_t l_Lake_platformTrace___closed__0;
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArtifact(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_collectArray___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_platformTrace___closed__3;
static lean_object* l_Lake_BuildMetadata_toJson___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildO___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_inputDir___closed__0;
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0;
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildAction___redArg___closed__0;
extern lean_object* l_Lake_instDataKindFilePath;
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildSharedLib___closed__0;
lean_object* lean_array_to_list(lean_object*);
static lean_object* l_Lake_buildO___lam__2___closed__2;
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instAlternativeELogTOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheEnabled___at___00Lake_buildArtifactUnlessUpToDate_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_OutputStatus_ofMTimeCheck(uint8_t);
lean_object* l_Lake_Cache_readOutputs_x3f(lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__7;
static lean_object* l_Prod_fromJson_x3f___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_serializeInputs(lean_object*);
lean_object* l_Lake_copyFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5(lean_object*);
static lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lake_cacheFileHash(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofFetch(uint64_t, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__17;
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___redArg(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__6;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_platformTrace___closed__4;
static lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__7;
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_toJson___closed__4;
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EquipT_instFunctor___redArg(lean_object*);
static lean_object* l_Lake_buildLeanSharedLib___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t);
static lean_object* l_Lake_instToJsonBuildMetadata___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__15;
lean_object* l_Lake_ArtifactDescr_fromJson_x3f(lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_serializeInputs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_getArtifacts_x3f___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0(uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildLeanO___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Hash_ofJsonNumber_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lake_writeFileHash___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_toJson___closed__5;
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_IO_FS_instOrdSystemTime_ord(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_IO_FS_readFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonPUnit___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_buildStaticLib___lam__1___closed__0;
static lean_object* l_Lake_BuildMetadata_toJson___closed__6;
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ok_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofStub___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPureTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lake_Hash_load_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_invalid_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Package_cacheScope(lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputFile(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__9;
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lake_EquipT_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern uint64_t l_Lake_Hash_nil;
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofFetch___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheEnabled___at___00Lake_buildArtifactUnlessUpToDate_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildFileUnlessUpToDate_x27___closed__0;
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonArtifact___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4(size_t, size_t, lean_object*);
static lean_object* l_Prod_toJson___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_instDataKindDynlib;
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(lean_object*);
lean_object* l_Lake_Artifact_trace(lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ofNat___boxed(lean_object*);
static lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1___closed__0;
LEAN_EXPORT lean_object* l_Lake_cacheArtifact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t);
static lean_object* l_Lake_addPureTrace___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArtifact___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Lake_OutputStatus_isCacheable(uint8_t);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__4;
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildO___closed__1;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lake_Job_async___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_readTraceFile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqOutputStatus___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__18;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_LeanInstall_ccLinkFlags(uint8_t, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1;
uint8_t l_Lake_JobAction_merge(uint8_t, uint8_t);
LEAN_EXPORT uint64_t l_Lake_buildO___lam__0(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___redArg(lean_object*);
static lean_object* l_Lake_Cache_saveArtifact___closed__2;
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonBuildMetadata;
lean_object* l_String_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_MTime_checkUpToDate___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__20;
static lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__9;
LEAN_EXPORT lean_object* l_Lake_OutputStatus_isUpToDate___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_missing_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_toCtorIdx(uint8_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lake_compileStaticLib(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
static lean_object* l_Lake_buildLeanO___lam__0___closed__2;
lean_object* l_Lake_EStateT_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_OutputStatus_isUpToDate(uint8_t);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJsonObject_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lake_writeFetchTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_computeBinFileHash(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lake_buildO___lam__2___closed__1;
static lean_object* l_Lake_BuildMetadata_toJson___closed__2;
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArtifact___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_inputBinFile___redArg___closed__0;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__5;
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7(lean_object*);
static lean_object* l_Lake_Cache_saveArtifact___closed__1;
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_writeFile(lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__16;
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__19;
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_addPureTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_isCacheable___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsArtifactOfMonadWorkspaceOfMonadLiftTBaseIOOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_toJson___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lake_instDecidableEqHash___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_readBinFile(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_instResolveOutputsArtifactOfMonadWorkspaceOfMonadLiftTBaseIOOfMonad___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_inputDir___lam__1___closed__0;
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_clearFileHash___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2___boxed__const__1;
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
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___boxed(lean_object**);
static lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___redArg___boxed(lean_object*);
static lean_object* l_Lake_platformTrace___closed__5;
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_Hash_fromJson_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_clearFileHash(lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheFileHash___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_decidableLT___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJson_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
x_1 = l_Lake_instMonadWorkspaceJobM___closed__10;
x_2 = lean_alloc_closure((void*)(l_ReaderT_read), 4, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instMonadWorkspaceJobM___closed__13;
x_2 = l_Lake_instMonadWorkspaceJobM___closed__14;
x_3 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instMonadWorkspaceJobM___closed__0;
x_2 = l_Lake_instAlternativeELogTOfMonad___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instMonadST___lam__2___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instMonadWorkspaceJobM___closed__17;
x_2 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instMonadWorkspaceJobM___closed__13;
x_2 = l_Lake_instMonadWorkspaceJobM___closed__15;
x_3 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instMonadWorkspaceJobM___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instMonadWorkspaceJobM___closed__19;
x_2 = l_Lake_instMonadWorkspaceJobM___closed__18;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
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
x_20 = l_Lake_instMonadWorkspaceJobM___closed__16;
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
x_26 = l_Lake_instMonadWorkspaceJobM___closed__20;
lean_inc_ref(x_19);
x_27 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_26, x_19);
x_28 = l_ReaderT_instMonad___redArg(x_22);
x_29 = lean_ctor_get(x_28, 0);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_29, 0);
lean_inc_ref(x_30);
lean_dec_ref(x_29);
x_31 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_27, x_19);
x_32 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(x_32, 0, lean_box(0));
lean_closure_set(x_32, 1, lean_box(0));
lean_closure_set(x_32, 2, lean_box(0));
lean_closure_set(x_32, 3, lean_box(0));
lean_closure_set(x_32, 4, x_31);
lean_inc_ref(x_25);
x_33 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_32, x_25);
lean_inc_ref(x_30);
x_34 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_34, 0, x_30);
x_35 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_35, 0, x_30);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_ReaderT_instMonad___redArg(x_28);
x_38 = lean_ctor_get(x_37, 0);
lean_inc_ref(x_38);
x_39 = lean_ctor_get(x_38, 0);
lean_inc_ref(x_39);
lean_dec_ref(x_38);
x_40 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_33, x_25);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_41, 0, lean_box(0));
lean_closure_set(x_41, 1, x_40);
lean_inc_ref(x_36);
x_42 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_41, x_36);
x_43 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_42, x_36);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_44, 0, lean_box(0));
lean_closure_set(x_44, 1, x_43);
lean_inc_ref(x_39);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_45, 0, x_39);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_46, 0, x_39);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_inc_ref(x_47);
x_48 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_44, x_47);
lean_inc_ref(x_47);
x_49 = l_Lake_EquipT_instFunctor___redArg(x_47);
x_50 = !lean_is_exclusive(x_37);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_51 = lean_ctor_get(x_37, 0);
x_52 = lean_ctor_get(x_37, 1);
lean_dec(x_52);
x_53 = lean_ctor_get(x_51, 0);
lean_inc_ref(x_53);
lean_dec_ref(x_51);
x_54 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_48, x_47);
x_55 = lean_alloc_closure((void*)(l_Lake_EquipT_lift___boxed), 5, 4);
lean_closure_set(x_55, 0, lean_box(0));
lean_closure_set(x_55, 1, lean_box(0));
lean_closure_set(x_55, 2, lean_box(0));
lean_closure_set(x_55, 3, x_54);
lean_inc_ref(x_49);
x_56 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_55, x_49);
x_57 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_56, x_49);
x_58 = lean_alloc_closure((void*)(l_Lake_JobM_runFetchM___boxed), 9, 2);
lean_closure_set(x_58, 0, lean_box(0));
lean_closure_set(x_58, 1, x_57);
lean_inc_ref(x_53);
x_59 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_59, 0, x_53);
x_60 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_60, 0, x_53);
lean_ctor_set(x_37, 1, x_60);
lean_ctor_set(x_37, 0, x_59);
x_61 = l_Lake_EquipT_instFunctor___redArg(x_37);
x_62 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_58, x_61);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_63 = lean_ctor_get(x_37, 0);
lean_inc(x_63);
lean_dec(x_37);
x_64 = lean_ctor_get(x_63, 0);
lean_inc_ref(x_64);
lean_dec_ref(x_63);
x_65 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_48, x_47);
x_66 = lean_alloc_closure((void*)(l_Lake_EquipT_lift___boxed), 5, 4);
lean_closure_set(x_66, 0, lean_box(0));
lean_closure_set(x_66, 1, lean_box(0));
lean_closure_set(x_66, 2, lean_box(0));
lean_closure_set(x_66, 3, x_65);
lean_inc_ref(x_49);
x_67 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_66, x_49);
x_68 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_67, x_49);
x_69 = lean_alloc_closure((void*)(l_Lake_JobM_runFetchM___boxed), 9, 2);
lean_closure_set(x_69, 0, lean_box(0));
lean_closure_set(x_69, 1, x_68);
lean_inc_ref(x_64);
x_70 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_70, 0, x_64);
x_71 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_71, 0, x_64);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lake_EquipT_instFunctor___redArg(x_72);
x_74 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_69, x_73);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_75 = lean_ctor_get(x_1, 1);
x_76 = lean_ctor_get(x_3, 0);
x_77 = lean_ctor_get(x_3, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_3);
lean_inc(x_75);
lean_inc(x_77);
x_78 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_78, 0, x_77);
lean_closure_set(x_78, 1, x_75);
lean_inc(x_75);
lean_inc(x_77);
x_79 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_79, 0, x_77);
lean_closure_set(x_79, 1, x_75);
lean_inc_ref(x_78);
lean_inc(x_77);
x_80 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_80, 0, x_77);
lean_closure_set(x_80, 1, x_78);
lean_inc(x_77);
lean_inc_ref(x_76);
x_81 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_81, 0, x_76);
lean_closure_set(x_81, 1, x_77);
lean_closure_set(x_81, 2, x_75);
x_82 = l_Lake_EStateT_instFunctor___redArg(x_76);
x_83 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_83, 0, x_77);
lean_inc_ref(x_82);
x_84 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_84, 2, x_81);
lean_ctor_set(x_84, 3, x_80);
lean_ctor_set(x_84, 4, x_79);
lean_ctor_set(x_1, 1, x_78);
lean_ctor_set(x_1, 0, x_84);
lean_inc_ref(x_82);
x_85 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_85, 0, x_82);
x_86 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_86, 0, x_82);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lake_instMonadWorkspaceJobM___closed__16;
lean_inc_ref(x_1);
x_89 = l_ReaderT_instAlternativeOfMonad___redArg(x_88, x_1);
x_90 = l_ReaderT_instMonad___redArg(x_1);
lean_inc_ref(x_90);
x_91 = l_ReaderT_instAlternativeOfMonad___redArg(x_89, x_90);
x_92 = lean_ctor_get(x_91, 0);
lean_inc_ref(x_92);
lean_dec_ref(x_91);
x_93 = lean_ctor_get(x_92, 0);
lean_inc_ref(x_93);
lean_dec_ref(x_92);
x_94 = l_Lake_instMonadWorkspaceJobM___closed__20;
lean_inc_ref(x_87);
x_95 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_94, x_87);
x_96 = l_ReaderT_instMonad___redArg(x_90);
x_97 = lean_ctor_get(x_96, 0);
lean_inc_ref(x_97);
x_98 = lean_ctor_get(x_97, 0);
lean_inc_ref(x_98);
lean_dec_ref(x_97);
x_99 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_95, x_87);
x_100 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(x_100, 0, lean_box(0));
lean_closure_set(x_100, 1, lean_box(0));
lean_closure_set(x_100, 2, lean_box(0));
lean_closure_set(x_100, 3, lean_box(0));
lean_closure_set(x_100, 4, x_99);
lean_inc_ref(x_93);
x_101 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_100, x_93);
lean_inc_ref(x_98);
x_102 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_102, 0, x_98);
x_103 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_103, 0, x_98);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_ReaderT_instMonad___redArg(x_96);
x_106 = lean_ctor_get(x_105, 0);
lean_inc_ref(x_106);
x_107 = lean_ctor_get(x_106, 0);
lean_inc_ref(x_107);
lean_dec_ref(x_106);
x_108 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_101, x_93);
x_109 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_109, 0, lean_box(0));
lean_closure_set(x_109, 1, x_108);
lean_inc_ref(x_104);
x_110 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_109, x_104);
x_111 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_110, x_104);
x_112 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_112, 0, lean_box(0));
lean_closure_set(x_112, 1, x_111);
lean_inc_ref(x_107);
x_113 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_113, 0, x_107);
x_114 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_114, 0, x_107);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
lean_inc_ref(x_115);
x_116 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_112, x_115);
lean_inc_ref(x_115);
x_117 = l_Lake_EquipT_instFunctor___redArg(x_115);
x_118 = lean_ctor_get(x_105, 0);
lean_inc_ref(x_118);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_119 = x_105;
} else {
 lean_dec_ref(x_105);
 x_119 = lean_box(0);
}
x_120 = lean_ctor_get(x_118, 0);
lean_inc_ref(x_120);
lean_dec_ref(x_118);
x_121 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_116, x_115);
x_122 = lean_alloc_closure((void*)(l_Lake_EquipT_lift___boxed), 5, 4);
lean_closure_set(x_122, 0, lean_box(0));
lean_closure_set(x_122, 1, lean_box(0));
lean_closure_set(x_122, 2, lean_box(0));
lean_closure_set(x_122, 3, x_121);
lean_inc_ref(x_117);
x_123 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_122, x_117);
x_124 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_123, x_117);
x_125 = lean_alloc_closure((void*)(l_Lake_JobM_runFetchM___boxed), 9, 2);
lean_closure_set(x_125, 0, lean_box(0));
lean_closure_set(x_125, 1, x_124);
lean_inc_ref(x_120);
x_126 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_126, 0, x_120);
x_127 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_127, 0, x_120);
if (lean_is_scalar(x_119)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_119;
}
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = l_Lake_EquipT_instFunctor___redArg(x_128);
x_130 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_125, x_129);
return x_130;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_131 = lean_ctor_get(x_1, 0);
x_132 = lean_ctor_get(x_1, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_1);
x_133 = lean_ctor_get(x_131, 0);
lean_inc_ref(x_133);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 lean_ctor_release(x_131, 2);
 lean_ctor_release(x_131, 3);
 lean_ctor_release(x_131, 4);
 x_135 = x_131;
} else {
 lean_dec_ref(x_131);
 x_135 = lean_box(0);
}
lean_inc(x_132);
lean_inc(x_134);
x_136 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_136, 0, x_134);
lean_closure_set(x_136, 1, x_132);
lean_inc(x_132);
lean_inc(x_134);
x_137 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_137, 0, x_134);
lean_closure_set(x_137, 1, x_132);
lean_inc_ref(x_136);
lean_inc(x_134);
x_138 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_138, 0, x_134);
lean_closure_set(x_138, 1, x_136);
lean_inc(x_134);
lean_inc_ref(x_133);
x_139 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_139, 0, x_133);
lean_closure_set(x_139, 1, x_134);
lean_closure_set(x_139, 2, x_132);
x_140 = l_Lake_EStateT_instFunctor___redArg(x_133);
x_141 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_141, 0, x_134);
lean_inc_ref(x_140);
if (lean_is_scalar(x_135)) {
 x_142 = lean_alloc_ctor(0, 5, 0);
} else {
 x_142 = x_135;
}
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
lean_ctor_set(x_142, 2, x_139);
lean_ctor_set(x_142, 3, x_138);
lean_ctor_set(x_142, 4, x_137);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_136);
lean_inc_ref(x_140);
x_144 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_144, 0, x_140);
x_145 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_145, 0, x_140);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
x_147 = l_Lake_instMonadWorkspaceJobM___closed__16;
lean_inc_ref(x_143);
x_148 = l_ReaderT_instAlternativeOfMonad___redArg(x_147, x_143);
x_149 = l_ReaderT_instMonad___redArg(x_143);
lean_inc_ref(x_149);
x_150 = l_ReaderT_instAlternativeOfMonad___redArg(x_148, x_149);
x_151 = lean_ctor_get(x_150, 0);
lean_inc_ref(x_151);
lean_dec_ref(x_150);
x_152 = lean_ctor_get(x_151, 0);
lean_inc_ref(x_152);
lean_dec_ref(x_151);
x_153 = l_Lake_instMonadWorkspaceJobM___closed__20;
lean_inc_ref(x_146);
x_154 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_153, x_146);
x_155 = l_ReaderT_instMonad___redArg(x_149);
x_156 = lean_ctor_get(x_155, 0);
lean_inc_ref(x_156);
x_157 = lean_ctor_get(x_156, 0);
lean_inc_ref(x_157);
lean_dec_ref(x_156);
x_158 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_154, x_146);
x_159 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(x_159, 0, lean_box(0));
lean_closure_set(x_159, 1, lean_box(0));
lean_closure_set(x_159, 2, lean_box(0));
lean_closure_set(x_159, 3, lean_box(0));
lean_closure_set(x_159, 4, x_158);
lean_inc_ref(x_152);
x_160 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_159, x_152);
lean_inc_ref(x_157);
x_161 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_161, 0, x_157);
x_162 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_162, 0, x_157);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
x_164 = l_ReaderT_instMonad___redArg(x_155);
x_165 = lean_ctor_get(x_164, 0);
lean_inc_ref(x_165);
x_166 = lean_ctor_get(x_165, 0);
lean_inc_ref(x_166);
lean_dec_ref(x_165);
x_167 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_160, x_152);
x_168 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_168, 0, lean_box(0));
lean_closure_set(x_168, 1, x_167);
lean_inc_ref(x_163);
x_169 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_168, x_163);
x_170 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_169, x_163);
x_171 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_171, 0, lean_box(0));
lean_closure_set(x_171, 1, x_170);
lean_inc_ref(x_166);
x_172 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_172, 0, x_166);
x_173 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_173, 0, x_166);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
lean_inc_ref(x_174);
x_175 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_171, x_174);
lean_inc_ref(x_174);
x_176 = l_Lake_EquipT_instFunctor___redArg(x_174);
x_177 = lean_ctor_get(x_164, 0);
lean_inc_ref(x_177);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_178 = x_164;
} else {
 lean_dec_ref(x_164);
 x_178 = lean_box(0);
}
x_179 = lean_ctor_get(x_177, 0);
lean_inc_ref(x_179);
lean_dec_ref(x_177);
x_180 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_175, x_174);
x_181 = lean_alloc_closure((void*)(l_Lake_EquipT_lift___boxed), 5, 4);
lean_closure_set(x_181, 0, lean_box(0));
lean_closure_set(x_181, 1, lean_box(0));
lean_closure_set(x_181, 2, lean_box(0));
lean_closure_set(x_181, 3, x_180);
lean_inc_ref(x_176);
x_182 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_181, x_176);
x_183 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(x_182, x_176);
x_184 = lean_alloc_closure((void*)(l_Lake_JobM_runFetchM___boxed), 9, 2);
lean_closure_set(x_184, 0, lean_box(0));
lean_closure_set(x_184, 1, x_183);
lean_inc_ref(x_179);
x_185 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_185, 0, x_179);
x_186 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_186, 0, x_179);
if (lean_is_scalar(x_178)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_178;
}
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
x_188 = l_Lake_EquipT_instFunctor___redArg(x_187);
x_189 = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(x_184, x_188);
return x_189;
}
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
x_2 = l_Lake_Hash_nil;
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
static lean_object* _init_l_Lake_platformTrace___closed__5() {
_start:
{
lean_object* x_1; uint64_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_platformTrace___closed__4;
x_2 = l_Lake_platformTrace___closed__1;
x_3 = l_Lake_platformTrace___closed__2;
x_4 = l_System_Platform_target;
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
x_1 = l_Lake_platformTrace___closed__5;
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
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_addPlatformTrace___redArg(x_1);
return x_3;
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
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_addLeanTrace___redArg(x_1, x_2);
return x_4;
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
x_10 = l_Lake_platformTrace___closed__2;
x_11 = l_Lake_addPureTrace___redArg___closed__0;
x_12 = lean_string_append(x_4, x_11);
x_13 = lean_apply_1(x_1, x_3);
x_14 = lean_string_append(x_12, x_13);
lean_dec_ref(x_13);
x_15 = l_Lake_platformTrace___closed__4;
x_16 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_10);
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
x_26 = l_Lake_platformTrace___closed__2;
x_27 = l_Lake_addPureTrace___redArg___closed__0;
x_28 = lean_string_append(x_4, x_27);
x_29 = lean_apply_1(x_1, x_3);
x_30 = lean_string_append(x_28, x_29);
lean_dec_ref(x_29);
x_31 = l_Lake_platformTrace___closed__4;
x_32 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_26);
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
LEAN_EXPORT lean_object* l_Lake_addPureTrace___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_addPureTrace___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
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
x_16 = l_Lake_platformTrace___closed__2;
x_17 = l_Lake_addPureTrace___redArg___closed__0;
x_18 = lean_string_append(x_5, x_17);
x_19 = lean_apply_1(x_2, x_4);
x_20 = lean_string_append(x_18, x_19);
lean_dec_ref(x_19);
x_21 = l_Lake_platformTrace___closed__4;
x_22 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_16);
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
x_32 = l_Lake_platformTrace___closed__2;
x_33 = l_Lake_addPureTrace___redArg___closed__0;
x_34 = lean_string_append(x_5, x_33);
x_35 = lean_apply_1(x_2, x_4);
x_36 = lean_string_append(x_34, x_35);
lean_dec_ref(x_35);
x_37 = l_Lake_platformTrace___closed__4;
x_38 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_32);
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
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Prod_toJson___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Prod_toJson___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__0(lean_object* x_1) {
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
x_5 = l_Prod_toJson___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__0___closed__0;
x_6 = lean_array_push(x_5, x_4);
x_7 = lean_array_push(x_6, x_3);
x_8 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = l_Prod_toJson___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__0(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__1(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2_spec__4(x_2, x_3, x_1);
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
x_13 = l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0(x_3);
x_14 = l_Lake_JsonObject_insertJson(x_11, x_12, x_13);
x_15 = l_Lake_BuildMetadata_toJson___closed__5;
x_16 = l_Option_toJson___at___00Lake_BuildMetadata_toJson_spec__1(x_4);
lean_dec(x_4);
x_17 = l_Lake_JsonObject_insertJson(x_14, x_15, x_16);
x_18 = l_Lake_BuildMetadata_toJson___closed__6;
x_19 = l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__2(x_5);
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
static lean_object* _init_l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___closed__0;
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
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3___closed__0;
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
static lean_object* _init_l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2___closed__0;
return x_2;
}
else
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3(x_1);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1(lean_object* x_1) {
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
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1_spec__2(x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__0;
x_7 = lean_unsigned_to_nat(80u);
x_8 = l_Lean_Json_pretty(x_1, x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec_ref(x_8);
x_10 = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
static lean_object* _init_l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1___closed__0;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1(x_1);
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
static lean_object* _init_l_Prod_fromJson_x3f___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected pair, got '", 20, 20);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7(lean_object* x_1) {
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
x_3 = l_Prod_fromJson_x3f___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__0;
x_4 = lean_unsigned_to_nat(80u);
x_5 = l_Lean_Json_pretty(x_2, x_4);
x_6 = lean_string_append(x_3, x_5);
lean_dec_ref(x_5);
x_7 = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_7 = l_Prod_fromJson_x3f___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7(x_6);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5(lean_object* x_1) {
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
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__8(x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__0;
x_7 = lean_unsigned_to_nat(80u);
x_8 = l_Lean_Json_pretty(x_1, x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec_ref(x_8);
x_10 = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
static lean_object* _init_l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3___closed__0;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5(x_1);
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
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint64_t x_5; uint8_t x_6; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint64_t x_13; lean_object* x_16; lean_object* x_17; uint64_t x_18; lean_object* x_19; lean_object* x_39; lean_object* x_40; uint64_t x_41; lean_object* x_44; uint64_t x_45; lean_object* x_46; lean_object* x_65; uint64_t x_66; uint64_t x_69; lean_object* x_70; uint64_t x_89; uint64_t x_92; lean_object* x_111; lean_object* x_112; 
x_111 = l_Lake_BuildMetadata_toJson___closed__0;
x_112 = l_Lake_JsonObject_getJson_x3f(x_1, x_111);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = l_Lake_BuildMetadata_toJson___closed__3;
x_114 = l_Lake_JsonObject_getJson_x3f(x_1, x_113);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; 
x_115 = l_Lake_BuildMetadata_fromJsonObject_x3f___closed__7;
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
lean_dec_ref(x_114);
x_117 = l_Lean_Json_getStr_x3f(x_116);
if (lean_obj_tag(x_117) == 0)
{
uint8_t x_118; 
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_117, 0);
x_120 = l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8;
x_121 = lean_string_append(x_120, x_119);
lean_dec(x_119);
lean_ctor_set(x_117, 0, x_121);
return x_117;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_117, 0);
lean_inc(x_122);
lean_dec(x_117);
x_123 = l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8;
x_124 = lean_string_append(x_123, x_122);
lean_dec(x_122);
x_125 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_125, 0, x_124);
return x_125;
}
}
else
{
if (lean_obj_tag(x_117) == 0)
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_117);
if (x_126 == 0)
{
lean_ctor_set_tag(x_117, 0);
return x_117;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_117, 0);
lean_inc(x_127);
lean_dec(x_117);
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_127);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_117, 0);
lean_inc(x_129);
lean_dec_ref(x_117);
x_130 = l_Lake_Hash_ofDecimal_x3f(x_129);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; 
x_131 = l_Lake_BuildMetadata_fromJsonObject_x3f___closed__10;
return x_131;
}
else
{
lean_object* x_132; uint64_t x_133; 
x_132 = lean_ctor_get(x_130, 0);
lean_inc(x_132);
lean_dec_ref(x_130);
x_133 = lean_unbox_uint64(x_132);
lean_dec(x_132);
x_92 = x_133;
goto block_110;
}
}
}
}
}
else
{
lean_object* x_134; lean_object* x_135; 
lean_dec_ref(x_112);
x_134 = l_Lake_BuildMetadata_toJson___closed__3;
x_135 = l_Lake_JsonObject_getJson_x3f(x_1, x_134);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; 
x_136 = l_Lake_BuildMetadata_fromJsonObject_x3f___closed__7;
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_135, 0);
lean_inc(x_137);
lean_dec_ref(x_135);
x_138 = l_Lake_Hash_fromJson_x3f(x_137);
if (lean_obj_tag(x_138) == 0)
{
uint8_t x_139; 
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_138, 0);
x_141 = l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8;
x_142 = lean_string_append(x_141, x_140);
lean_dec(x_140);
lean_ctor_set(x_138, 0, x_142);
return x_138;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_143 = lean_ctor_get(x_138, 0);
lean_inc(x_143);
lean_dec(x_138);
x_144 = l_Lake_BuildMetadata_fromJsonObject_x3f___closed__8;
x_145 = lean_string_append(x_144, x_143);
lean_dec(x_143);
x_146 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_146, 0, x_145);
return x_146;
}
}
else
{
if (lean_obj_tag(x_138) == 0)
{
uint8_t x_147; 
x_147 = !lean_is_exclusive(x_138);
if (x_147 == 0)
{
lean_ctor_set_tag(x_138, 0);
return x_138;
}
else
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_138, 0);
lean_inc(x_148);
lean_dec(x_138);
x_149 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_149, 0, x_148);
return x_149;
}
}
else
{
lean_object* x_150; uint64_t x_151; 
x_150 = lean_ctor_get(x_138, 0);
lean_inc(x_150);
lean_dec_ref(x_138);
x_151 = lean_unbox_uint64(x_150);
lean_dec(x_150);
x_92 = x_151;
goto block_110;
}
}
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set_uint64(x_7, sizeof(void*)*3, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*3 + 8, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
block_15:
{
uint8_t x_14; 
x_14 = 0;
x_2 = x_11;
x_3 = x_10;
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
x_10 = x_16;
x_11 = x_17;
x_12 = x_19;
x_13 = x_18;
goto block_15;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0(x_22);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec_ref(x_16);
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
lean_dec(x_17);
lean_dec_ref(x_16);
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
x_10 = x_16;
x_11 = x_17;
x_12 = x_19;
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
x_2 = x_17;
x_3 = x_16;
x_4 = x_19;
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
x_16 = x_40;
x_17 = x_39;
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
x_39 = x_46;
x_40 = x_44;
x_41 = x_45;
goto block_43;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
x_50 = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1(x_49);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
lean_dec(x_46);
lean_dec_ref(x_44);
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
lean_dec_ref(x_44);
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
x_39 = x_46;
x_40 = x_44;
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
block_88:
{
lean_object* x_71; lean_object* x_72; 
x_71 = l_Lake_BuildMetadata_toJson___closed__5;
x_72 = l_Lake_JsonObject_getJson_x3f(x_1, x_71);
if (lean_obj_tag(x_72) == 0)
{
x_65 = x_70;
x_66 = x_69;
goto block_68;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec_ref(x_72);
x_74 = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2(x_73);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; 
lean_dec_ref(x_70);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_74, 0);
x_77 = l_Lake_BuildMetadata_fromJsonObject_x3f___closed__3;
x_78 = lean_string_append(x_77, x_76);
lean_dec(x_76);
lean_ctor_set(x_74, 0, x_78);
return x_74;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_74, 0);
lean_inc(x_79);
lean_dec(x_74);
x_80 = l_Lake_BuildMetadata_fromJsonObject_x3f___closed__3;
x_81 = lean_string_append(x_80, x_79);
lean_dec(x_79);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
else
{
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_83; 
lean_dec_ref(x_70);
x_83 = !lean_is_exclusive(x_74);
if (x_83 == 0)
{
lean_ctor_set_tag(x_74, 0);
return x_74;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_74, 0);
lean_inc(x_84);
lean_dec(x_74);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
else
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_74, 0);
lean_inc(x_86);
lean_dec_ref(x_74);
if (lean_obj_tag(x_86) == 0)
{
x_65 = x_70;
x_66 = x_69;
goto block_68;
}
else
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
x_44 = x_70;
x_45 = x_69;
x_46 = x_87;
goto block_64;
}
}
}
}
}
block_91:
{
lean_object* x_90; 
x_90 = l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4;
x_69 = x_89;
x_70 = x_90;
goto block_88;
}
block_110:
{
lean_object* x_93; lean_object* x_94; 
x_93 = l_Lake_BuildMetadata_toJson___closed__4;
x_94 = l_Lake_JsonObject_getJson_x3f(x_1, x_93);
if (lean_obj_tag(x_94) == 0)
{
x_89 = x_92;
goto block_91;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
lean_dec_ref(x_94);
x_96 = l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3(x_95);
if (lean_obj_tag(x_96) == 0)
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_96, 0);
x_99 = l_Lake_BuildMetadata_fromJsonObject_x3f___closed__5;
x_100 = lean_string_append(x_99, x_98);
lean_dec(x_98);
lean_ctor_set(x_96, 0, x_100);
return x_96;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_96, 0);
lean_inc(x_101);
lean_dec(x_96);
x_102 = l_Lake_BuildMetadata_fromJsonObject_x3f___closed__5;
x_103 = lean_string_append(x_102, x_101);
lean_dec(x_101);
x_104 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_104, 0, x_103);
return x_104;
}
}
else
{
if (lean_obj_tag(x_96) == 0)
{
uint8_t x_105; 
x_105 = !lean_is_exclusive(x_96);
if (x_105 == 0)
{
lean_ctor_set_tag(x_96, 0);
return x_96;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_96, 0);
lean_inc(x_106);
lean_dec(x_96);
x_107 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
}
else
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_96, 0);
lean_inc(x_108);
lean_dec_ref(x_96);
if (lean_obj_tag(x_108) == 0)
{
x_89 = x_92;
goto block_91;
}
else
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_dec_ref(x_108);
x_69 = x_92;
x_70 = x_109;
goto block_88;
}
}
}
}
}
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
x_1 = lean_mk_string_unchecked("unknown trace format: ", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid trace: ", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown trace format: expected JSON number or object", 52, 52);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_BuildMetadata_fromJson_x3f___closed__3;
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
lean_object* x_22; lean_object* x_23; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_23 = x_21;
} else {
 lean_dec_ref(x_21);
 x_23 = lean_box(0);
}
x_28 = l_Lake_BuildMetadata_toJson___closed__0;
x_29 = l_Lake_JsonObject_getJson_x3f(x_20, x_28);
if (lean_obj_tag(x_29) == 1)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
if (lean_obj_tag(x_30) == 3)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0;
x_34 = lean_string_dec_eq(x_32, x_33);
lean_dec_ref(x_32);
if (x_34 == 0)
{
lean_free_object(x_30);
goto block_27;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_23);
x_35 = l_Lake_BuildMetadata_fromJson_x3f___closed__2;
x_36 = lean_string_append(x_35, x_22);
lean_dec(x_22);
lean_ctor_set_tag(x_30, 0);
lean_ctor_set(x_30, 0, x_36);
return x_30;
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_30, 0);
lean_inc(x_37);
lean_dec(x_30);
x_38 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0;
x_39 = lean_string_dec_eq(x_37, x_38);
lean_dec_ref(x_37);
if (x_39 == 0)
{
goto block_27;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_23);
x_40 = l_Lake_BuildMetadata_fromJson_x3f___closed__2;
x_41 = lean_string_append(x_40, x_22);
lean_dec(x_22);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
else
{
lean_dec(x_30);
goto block_27;
}
}
else
{
lean_dec(x_29);
goto block_27;
}
block_27:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = l_Lake_BuildMetadata_fromJson_x3f___closed__1;
x_25 = lean_string_append(x_24, x_22);
lean_dec(x_22);
if (lean_is_scalar(x_23)) {
 x_26 = lean_alloc_ctor(0, 1, 0);
} else {
 x_26 = x_23;
}
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
return x_21;
}
}
default: 
{
lean_object* x_43; 
x_43 = l_Lake_BuildMetadata_fromJson_x3f___closed__4;
return x_43;
}
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
x_19 = l_Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0(x_18);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_serializeInputs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lake_BuildMetadata_fromJsonObject_x3f___closed__4;
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
if (x_5 == 0)
{
return x_3;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
if (x_5 == 0)
{
return x_3;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(x_1, x_7, x_8, x_3);
return x_9;
}
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_4);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(x_1, x_10, x_11, x_3);
return x_12;
}
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
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
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_BuildMetadata_ofBuild___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
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
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_writeFile(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
lean_inc_ref(x_1);
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
lean_dec_ref(x_1);
return x_8;
}
else
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_writeFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_BuildMetadata_writeFile(x_1, x_2);
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
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_writeBuildTrace___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_7;
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
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_writeBuildTrace(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_4);
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
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OutputStatus_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
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
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OutputStatus_outOfDate_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_outOfDate_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
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
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OutputStatus_mtimeUpToDate_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_mtimeUpToDate_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
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
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OutputStatus_hashUpToDate_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_OutputStatus_hashUpToDate_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
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
x_2 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_12, x_13);
return x_15;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(x_1, x_7, x_8, x_4, x_5);
lean_dec_ref(x_1);
return x_9;
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
if (x_12 == 0)
{
lean_object* x_15; 
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
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(x_1, x_16, x_17, x_11, x_7);
return x_18;
}
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_10);
x_21 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(x_1, x_19, x_20, x_11, x_7);
return x_21;
}
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(x_1, x_2, x_3, x_4, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_14;
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
uint8_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; 
x_31 = lean_ctor_get_uint8(x_21, sizeof(void*)*3);
x_32 = 1;
x_33 = l_Lake_JobAction_merge(x_31, x_32);
lean_ctor_set_uint8(x_21, sizeof(void*)*3, x_33);
x_34 = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(x_17, x_7, x_8, x_9, x_10, x_11, x_21);
lean_dec_ref(x_17);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec_ref(x_34);
x_23 = x_35;
x_24 = lean_box(0);
goto block_26;
}
else
{
uint8_t x_36; 
lean_dec(x_22);
lean_dec(x_20);
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
return x_34;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_34, 0);
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_34);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_21, 0);
x_41 = lean_ctor_get_uint8(x_21, sizeof(void*)*3);
x_42 = lean_ctor_get(x_21, 1);
x_43 = lean_ctor_get(x_21, 2);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_40);
lean_dec(x_21);
x_44 = 1;
x_45 = l_Lake_JobAction_merge(x_41, x_44);
x_46 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_42);
lean_ctor_set(x_46, 2, x_43);
lean_ctor_set_uint8(x_46, sizeof(void*)*3, x_45);
x_47 = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(x_17, x_7, x_8, x_9, x_10, x_11, x_46);
lean_dec_ref(x_17);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec_ref(x_47);
x_23 = x_48;
x_24 = lean_box(0);
goto block_26;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_22);
lean_dec(x_20);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_51 = x_47;
} else {
 lean_dec_ref(x_47);
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
lean_object* x_53; uint64_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_66; uint8_t x_67; uint8_t x_68; 
x_53 = lean_ctor_get(x_5, 0);
lean_inc(x_53);
lean_dec(x_5);
x_54 = lean_ctor_get_uint64(x_53, sizeof(void*)*3);
x_55 = lean_ctor_get(x_53, 2);
lean_inc_ref(x_55);
lean_dec_ref(x_53);
x_56 = lean_box_uint64(x_54);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg(x_1, x_2, x_3, x_4, x_57, x_6, x_11, x_12);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_61 = x_58;
} else {
 lean_dec_ref(x_58);
 x_61 = lean_box(0);
}
x_66 = 0;
x_67 = lean_unbox(x_59);
x_68 = l_Lake_instDecidableEqOutputStatus(x_67, x_66);
if (x_68 == 0)
{
lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; 
x_69 = lean_ctor_get(x_60, 0);
lean_inc_ref(x_69);
x_70 = lean_ctor_get_uint8(x_60, sizeof(void*)*3);
x_71 = lean_ctor_get(x_60, 1);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_60, 2);
lean_inc(x_72);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 lean_ctor_release(x_60, 2);
 x_73 = x_60;
} else {
 lean_dec_ref(x_60);
 x_73 = lean_box(0);
}
x_74 = 1;
x_75 = l_Lake_JobAction_merge(x_70, x_74);
if (lean_is_scalar(x_73)) {
 x_76 = lean_alloc_ctor(0, 3, 1);
} else {
 x_76 = x_73;
}
lean_ctor_set(x_76, 0, x_69);
lean_ctor_set(x_76, 1, x_71);
lean_ctor_set(x_76, 2, x_72);
lean_ctor_set_uint8(x_76, sizeof(void*)*3, x_75);
x_77 = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(x_55, x_7, x_8, x_9, x_10, x_11, x_76);
lean_dec_ref(x_55);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec_ref(x_77);
x_62 = x_78;
x_63 = lean_box(0);
goto block_65;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_61);
lean_dec(x_59);
x_79 = lean_ctor_get(x_77, 0);
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
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
else
{
lean_dec_ref(x_55);
x_62 = x_60;
x_63 = lean_box(0);
goto block_65;
}
block_65:
{
lean_object* x_64; 
if (lean_is_scalar(x_61)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_61;
}
lean_ctor_set(x_64, 0, x_59);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
}
else
{
lean_object* x_83; uint8_t x_84; 
lean_dec(x_5);
lean_dec_ref(x_1);
x_83 = lean_ctor_get(x_11, 0);
x_84 = lean_ctor_get_uint8(x_83, sizeof(void*)*2);
if (x_84 == 0)
{
uint8_t x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_85 = 0;
x_86 = lean_box(x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_12);
return x_87;
}
else
{
uint8_t x_88; 
x_88 = l_Lake_MTime_checkUpToDate___redArg(x_2, x_3, x_6);
if (x_88 == 0)
{
uint8_t x_89; lean_object* x_90; lean_object* x_91; 
x_89 = 0;
x_90 = lean_box(x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_12);
return x_91;
}
else
{
uint8_t x_92; lean_object* x_93; lean_object* x_94; 
x_92 = 1;
x_93 = lean_box(x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_12);
return x_94;
}
}
}
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
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
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
lean_object* x_14; 
x_14 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
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
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_14);
if (x_35 == 0)
{
return x_14;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_14, 0);
x_37 = lean_ctor_get(x_14, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_14);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
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
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
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
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_15);
if (x_36 == 0)
{
return x_15;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_15, 0);
x_38 = lean_ctor_get(x_15, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_15);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
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
lean_object* x_25; uint64_t x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_35; 
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
goto block_75;
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = lean_array_get_size(x_27);
x_77 = lean_unsigned_to_nat(0u);
x_78 = lean_nat_dec_eq(x_76, x_77);
if (x_78 == 0)
{
goto block_75;
}
else
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_3);
if (x_79 == 0)
{
uint8_t x_80; uint8_t x_81; uint8_t x_82; 
x_80 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_81 = 2;
x_82 = l_Lake_JobAction_merge(x_80, x_81);
lean_ctor_set_uint8(x_3, sizeof(void*)*3, x_82);
x_30 = x_3;
x_31 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; uint8_t x_88; lean_object* x_89; 
x_83 = lean_ctor_get(x_3, 0);
x_84 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_85 = lean_ctor_get(x_3, 1);
x_86 = lean_ctor_get(x_3, 2);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_83);
lean_dec(x_3);
x_87 = 2;
x_88 = l_Lake_JobAction_merge(x_84, x_87);
x_89 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_89, 0, x_83);
lean_ctor_set(x_89, 1, x_85);
lean_ctor_set(x_89, 2, x_86);
lean_ctor_set_uint8(x_89, sizeof(void*)*3, x_88);
x_30 = x_89;
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
block_41:
{
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec_ref(x_35);
x_30 = x_36;
x_31 = lean_box(0);
goto block_34;
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_35);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
block_75:
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_3);
if (x_42 == 0)
{
uint8_t x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_43 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_44 = 1;
x_45 = l_Lake_JobAction_merge(x_43, x_44);
lean_ctor_set_uint8(x_3, sizeof(void*)*3, x_45);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_array_get_size(x_27);
x_48 = lean_nat_dec_lt(x_46, x_47);
if (x_48 == 0)
{
x_30 = x_3;
x_31 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_box(0);
x_50 = lean_nat_dec_le(x_47, x_47);
if (x_50 == 0)
{
if (x_48 == 0)
{
x_30 = x_3;
x_31 = lean_box(0);
goto block_34;
}
else
{
size_t x_51; size_t x_52; lean_object* x_53; 
x_51 = 0;
x_52 = lean_usize_of_nat(x_47);
x_53 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(x_27, x_51, x_52, x_49, x_3);
x_35 = x_53;
goto block_41;
}
}
else
{
size_t x_54; size_t x_55; lean_object* x_56; 
x_54 = 0;
x_55 = lean_usize_of_nat(x_47);
x_56 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(x_27, x_54, x_55, x_49, x_3);
x_35 = x_56;
goto block_41;
}
}
}
else
{
lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_57 = lean_ctor_get(x_3, 0);
x_58 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_59 = lean_ctor_get(x_3, 1);
x_60 = lean_ctor_get(x_3, 2);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_57);
lean_dec(x_3);
x_61 = 1;
x_62 = l_Lake_JobAction_merge(x_58, x_61);
x_63 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_59);
lean_ctor_set(x_63, 2, x_60);
lean_ctor_set_uint8(x_63, sizeof(void*)*3, x_62);
x_64 = lean_unsigned_to_nat(0u);
x_65 = lean_array_get_size(x_27);
x_66 = lean_nat_dec_lt(x_64, x_65);
if (x_66 == 0)
{
x_30 = x_63;
x_31 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_box(0);
x_68 = lean_nat_dec_le(x_65, x_65);
if (x_68 == 0)
{
if (x_66 == 0)
{
x_30 = x_63;
x_31 = lean_box(0);
goto block_34;
}
else
{
size_t x_69; size_t x_70; lean_object* x_71; 
x_69 = 0;
x_70 = lean_usize_of_nat(x_65);
x_71 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(x_27, x_69, x_70, x_67, x_63);
x_35 = x_71;
goto block_41;
}
}
else
{
size_t x_72; size_t x_73; lean_object* x_74; 
x_72 = 0;
x_73 = lean_usize_of_nat(x_65);
x_74 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay_spec__0___redArg(x_27, x_72, x_73, x_67, x_63);
x_35 = x_74;
goto block_41;
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
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetchIfUpToDate(uint64_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(x_1, x_2, x_8);
return x_10;
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
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonPUnit___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Lake_instToOutputJsonPUnit___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instToOutputJsonPUnit___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instToOutputJsonPUnit() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instToOutputJsonPUnit___closed__0;
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
LEAN_EXPORT lean_object* l_Lake_instToOutputJsonArtifact___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instToOutputJsonArtifact___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instToOutputJsonArtifact___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instToOutputJsonArtifact___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instToOutputJsonArtifact() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instToOutputJsonArtifact___closed__0;
return x_1;
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
x_42 = l_Array_extract___redArg(x_36, x_40, x_41);
lean_inc(x_35);
x_43 = lean_apply_1(x_1, x_35);
x_44 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_2, x_43, x_42);
x_45 = l_Lake_BuildMetadata_writeFile(x_3, x_44);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
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
x_83 = l_Array_extract___redArg(x_77, x_81, x_82);
lean_inc(x_76);
x_84 = lean_apply_1(x_1, x_76);
x_85 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_2, x_84, x_83);
x_86 = l_Lake_BuildMetadata_writeFile(x_3, x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
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
lean_dec_ref(x_3);
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
x_128 = l_Array_extract___redArg(x_122, x_126, x_127);
lean_inc(x_120);
x_129 = lean_apply_1(x_1, x_120);
x_130 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_2, x_129, x_128);
x_131 = l_Lake_BuildMetadata_writeFile(x_3, x_130);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
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
lean_dec_ref(x_3);
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
lean_dec_ref(x_3);
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
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
x_14 = l_Lake_buildAction___redArg(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_2);
return x_14;
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
LEAN_EXPORT lean_object* l_Lake_buildAction___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_6);
x_15 = l_Lake_buildAction(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_3);
return x_15;
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
lean_ctor_set(x_14, 0, x_20);
x_21 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_1, x_2, x_3, x_4, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
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
x_30 = l_Lake_instToOutputJsonPUnit___closed__0;
x_31 = l_Lake_buildAction___redArg(x_30, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_24);
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
x_52 = l_Lake_instToOutputJsonPUnit___closed__0;
x_53 = l_Lake_buildAction___redArg(x_52, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_45);
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
x_63 = !lean_is_exclusive(x_21);
if (x_63 == 0)
{
return x_21;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_21, 0);
x_65 = lean_ctor_get(x_21, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_21);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
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
x_67 = !lean_is_exclusive(x_18);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_18, 1);
lean_ctor_set(x_14, 0, x_68);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_18, 0);
x_70 = lean_ctor_get(x_18, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_18);
lean_ctor_set(x_14, 0, x_70);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_14);
return x_71;
}
}
}
else
{
lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_14, 0);
x_73 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
x_74 = lean_ctor_get(x_14, 1);
x_75 = lean_ctor_get(x_14, 2);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_72);
lean_dec(x_14);
lean_inc_ref(x_5);
x_76 = l_Lake_readTraceFile(x_5, x_72);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec_ref(x_76);
x_79 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_74);
lean_ctor_set(x_79, 2, x_75);
lean_ctor_set_uint8(x_79, sizeof(void*)*3, x_73);
x_80 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_1, x_2, x_3, x_4, x_77, x_8, x_9, x_10, x_11, x_12, x_13, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; 
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
x_84 = 0;
x_85 = lean_unbox(x_81);
lean_dec(x_81);
x_86 = l_Lake_instDecidableEqOutputStatus(x_85, x_84);
if (x_86 == 0)
{
uint8_t x_87; lean_object* x_88; lean_object* x_89; 
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_87 = 1;
x_88 = lean_box(x_87);
if (lean_is_scalar(x_83)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_83;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_82);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_83);
x_90 = l_Lake_instToOutputJsonPUnit___closed__0;
x_91 = l_Lake_buildAction___redArg(x_90, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_82);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; 
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
x_94 = 0;
x_95 = lean_box(x_94);
if (lean_is_scalar(x_93)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_93;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_92);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_ctor_get(x_91, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_91, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_99 = x_91;
} else {
 lean_dec_ref(x_91);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_101 = lean_ctor_get(x_80, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_80, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_103 = x_80;
} else {
 lean_dec_ref(x_80);
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
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
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
x_105 = lean_ctor_get(x_76, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_76, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_107 = x_76;
} else {
 lean_dec_ref(x_76);
 x_107 = lean_box(0);
}
x_108 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_74);
lean_ctor_set(x_108, 2, x_75);
lean_ctor_set_uint8(x_108, sizeof(void*)*3, x_73);
if (lean_is_scalar(x_107)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_107;
}
lean_ctor_set(x_109, 0, x_105);
lean_ctor_set(x_109, 1, x_108);
return x_109;
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
lean_ctor_set(x_15, 0, x_21);
x_22 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_2, x_3, x_4, x_5, x_20, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
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
x_31 = l_Lake_instToOutputJsonPUnit___closed__0;
x_32 = l_Lake_buildAction___redArg(x_31, x_5, x_6, x_7, x_8, x_10, x_11, x_12, x_13, x_14, x_25);
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
x_53 = l_Lake_instToOutputJsonPUnit___closed__0;
x_54 = l_Lake_buildAction___redArg(x_53, x_5, x_6, x_7, x_8, x_10, x_11, x_12, x_13, x_14, x_46);
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
x_64 = !lean_is_exclusive(x_22);
if (x_64 == 0)
{
return x_22;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_22, 0);
x_66 = lean_ctor_get(x_22, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_22);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
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
x_68 = !lean_is_exclusive(x_19);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_19, 1);
lean_ctor_set(x_15, 0, x_69);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_19, 0);
x_71 = lean_ctor_get(x_19, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_19);
lean_ctor_set(x_15, 0, x_71);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_15);
return x_72;
}
}
}
else
{
lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_15, 0);
x_74 = lean_ctor_get_uint8(x_15, sizeof(void*)*3);
x_75 = lean_ctor_get(x_15, 1);
x_76 = lean_ctor_get(x_15, 2);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_73);
lean_dec(x_15);
lean_inc_ref(x_6);
x_77 = l_Lake_readTraceFile(x_6, x_73);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec_ref(x_77);
x_80 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_75);
lean_ctor_set(x_80, 2, x_76);
lean_ctor_set_uint8(x_80, sizeof(void*)*3, x_74);
x_81 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_2, x_3, x_4, x_5, x_78, x_9, x_10, x_11, x_12, x_13, x_14, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_84 = x_81;
} else {
 lean_dec_ref(x_81);
 x_84 = lean_box(0);
}
x_85 = 0;
x_86 = lean_unbox(x_82);
lean_dec(x_82);
x_87 = l_Lake_instDecidableEqOutputStatus(x_86, x_85);
if (x_87 == 0)
{
uint8_t x_88; lean_object* x_89; lean_object* x_90; 
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_88 = 1;
x_89 = lean_box(x_88);
if (lean_is_scalar(x_84)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_84;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_83);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_84);
x_91 = l_Lake_instToOutputJsonPUnit___closed__0;
x_92 = l_Lake_buildAction___redArg(x_91, x_5, x_6, x_7, x_8, x_10, x_11, x_12, x_13, x_14, x_83);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; 
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
x_95 = 0;
x_96 = lean_box(x_95);
if (lean_is_scalar(x_94)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_94;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_93);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_92, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_92, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_100 = x_92;
} else {
 lean_dec_ref(x_92);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_102 = lean_ctor_get(x_81, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_81, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_104 = x_81;
} else {
 lean_dec_ref(x_81);
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
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
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
x_106 = lean_ctor_get(x_77, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_77, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_108 = x_77;
} else {
 lean_dec_ref(x_77);
 x_108 = lean_box(0);
}
x_109 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_75);
lean_ctor_set(x_109, 2, x_76);
lean_ctor_set_uint8(x_109, sizeof(void*)*3, x_74);
if (lean_is_scalar(x_108)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_108;
}
lean_ctor_set(x_110, 0, x_106);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
lean_ctor_set(x_14, 0, x_25);
x_26 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_1, x_2, x_3, x_4, x_24, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_35; uint8_t x_36; uint8_t x_37; 
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
x_38 = l_Lake_instToOutputJsonPUnit___closed__0;
x_39 = l_Lake_buildAction___redArg(x_38, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_28);
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
x_43 = lean_ctor_get(x_26, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_26, 1);
lean_inc(x_44);
lean_dec_ref(x_26);
x_16 = x_43;
x_17 = x_44;
x_18 = lean_box(0);
goto block_20;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
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
x_45 = lean_ctor_get(x_23, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_23, 1);
lean_inc(x_46);
lean_dec_ref(x_23);
lean_ctor_set(x_14, 0, x_46);
x_16 = x_45;
x_17 = x_14;
x_18 = lean_box(0);
goto block_20;
}
}
else
{
lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_14, 0);
x_48 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
x_49 = lean_ctor_get(x_14, 1);
x_50 = lean_ctor_get(x_14, 2);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_47);
lean_dec(x_14);
lean_inc_ref(x_5);
x_51 = l_Lake_readTraceFile(x_5, x_47);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec_ref(x_51);
x_54 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_49);
lean_ctor_set(x_54, 2, x_50);
lean_ctor_set_uint8(x_54, sizeof(void*)*3, x_48);
x_55 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_1, x_2, x_3, x_4, x_52, x_8, x_9, x_10, x_11, x_12, x_13, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_64; uint8_t x_65; uint8_t x_66; 
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
x_59 = lean_box(0);
x_64 = 0;
x_65 = lean_unbox(x_56);
lean_dec(x_56);
x_66 = l_Lake_instDecidableEqOutputStatus(x_65, x_64);
if (x_66 == 0)
{
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_60 = x_57;
x_61 = lean_box(0);
goto block_63;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = l_Lake_instToOutputJsonPUnit___closed__0;
x_68 = l_Lake_buildAction___redArg(x_67, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_57);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec_ref(x_68);
x_60 = x_69;
x_61 = lean_box(0);
goto block_63;
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_58);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec_ref(x_68);
x_16 = x_70;
x_17 = x_71;
x_18 = lean_box(0);
goto block_20;
}
}
block_63:
{
lean_object* x_62; 
if (lean_is_scalar(x_58)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_58;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_72 = lean_ctor_get(x_55, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_55, 1);
lean_inc(x_73);
lean_dec_ref(x_55);
x_16 = x_72;
x_17 = x_73;
x_18 = lean_box(0);
goto block_20;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
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
x_74 = lean_ctor_get(x_51, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_51, 1);
lean_inc(x_75);
lean_dec_ref(x_51);
x_76 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_49);
lean_ctor_set(x_76, 2, x_50);
lean_ctor_set_uint8(x_76, sizeof(void*)*3, x_48);
x_16 = x_74;
x_17 = x_76;
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
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
lean_ctor_set(x_15, 0, x_26);
x_27 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_2, x_3, x_4, x_5, x_25, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_36; uint8_t x_37; uint8_t x_38; 
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
x_39 = l_Lake_instToOutputJsonPUnit___closed__0;
x_40 = l_Lake_buildAction___redArg(x_39, x_5, x_6, x_7, x_8, x_10, x_11, x_12, x_13, x_14, x_29);
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
x_44 = lean_ctor_get(x_27, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_27, 1);
lean_inc(x_45);
lean_dec_ref(x_27);
x_17 = x_44;
x_18 = x_45;
x_19 = lean_box(0);
goto block_21;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
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
x_46 = lean_ctor_get(x_24, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_24, 1);
lean_inc(x_47);
lean_dec_ref(x_24);
lean_ctor_set(x_15, 0, x_47);
x_17 = x_46;
x_18 = x_15;
x_19 = lean_box(0);
goto block_21;
}
}
else
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_15, 0);
x_49 = lean_ctor_get_uint8(x_15, sizeof(void*)*3);
x_50 = lean_ctor_get(x_15, 1);
x_51 = lean_ctor_get(x_15, 2);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_48);
lean_dec(x_15);
lean_inc_ref(x_6);
x_52 = l_Lake_readTraceFile(x_6, x_48);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec_ref(x_52);
x_55 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_50);
lean_ctor_set(x_55, 2, x_51);
lean_ctor_set_uint8(x_55, sizeof(void*)*3, x_49);
x_56 = l_Lake_SavedTrace_replayIfUpToDate_x27___redArg(x_2, x_3, x_4, x_5, x_53, x_9, x_10, x_11, x_12, x_13, x_14, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_65; uint8_t x_66; uint8_t x_67; 
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
x_60 = lean_box(0);
x_65 = 0;
x_66 = lean_unbox(x_57);
lean_dec(x_57);
x_67 = l_Lake_instDecidableEqOutputStatus(x_66, x_65);
if (x_67 == 0)
{
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_61 = x_58;
x_62 = lean_box(0);
goto block_64;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = l_Lake_instToOutputJsonPUnit___closed__0;
x_69 = l_Lake_buildAction___redArg(x_68, x_5, x_6, x_7, x_8, x_10, x_11, x_12, x_13, x_14, x_58);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec_ref(x_69);
x_61 = x_70;
x_62 = lean_box(0);
goto block_64;
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_59);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec_ref(x_69);
x_17 = x_71;
x_18 = x_72;
x_19 = lean_box(0);
goto block_21;
}
}
block_64:
{
lean_object* x_63; 
if (lean_is_scalar(x_59)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_59;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_73 = lean_ctor_get(x_56, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_56, 1);
lean_inc(x_74);
lean_dec_ref(x_56);
x_17 = x_73;
x_18 = x_74;
x_19 = lean_box(0);
goto block_21;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
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
x_75 = lean_ctor_get(x_52, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_52, 1);
lean_inc(x_76);
lean_dec_ref(x_52);
x_77 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_50);
lean_ctor_set(x_77, 2, x_51);
lean_ctor_set_uint8(x_77, sizeof(void*)*3, x_49);
x_17 = x_75;
x_18 = x_77;
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
lean_inc_ref(x_5);
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
if (lean_obj_tag(x_60) == 1)
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
else
{
lean_dec(x_60);
x_47 = x_4;
x_48 = lean_box(0);
goto block_59;
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
lean_inc_ref(x_9);
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
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_11);
lean_ctor_set(x_20, 2, x_10);
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
x_26 = lean_array_get_size(x_12);
x_27 = lean_array_push(x_12, x_25);
x_28 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_11);
lean_ctor_set(x_28, 2, x_10);
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
x_34 = lean_array_get_size(x_12);
x_35 = lean_array_push(x_12, x_33);
x_36 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_11);
lean_ctor_set(x_36, 2, x_10);
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
x_42 = lean_array_get_size(x_12);
x_43 = lean_array_push(x_12, x_41);
x_44 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_11);
lean_ctor_set(x_44, 2, x_10);
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
x_10 = x_52;
x_11 = x_51;
x_12 = x_49;
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
x_10 = x_57;
x_11 = x_56;
x_12 = x_54;
x_13 = x_55;
x_14 = x_58;
goto block_46;
}
}
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
LEAN_EXPORT lean_object* l_Lake_fetchFileHash(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_fetchFileHash___redArg(x_1, x_2, x_7, x_8);
return x_10;
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
x_17 = l_Lake_platformTrace___closed__2;
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
x_46 = l_Lake_platformTrace___closed__2;
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
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_fetchFileTrace___redArg(x_1, x_2, x_7, x_8);
return x_10;
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
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_44 = l_Array_extract___redArg(x_36, x_42, x_43);
x_45 = lean_box(0);
x_46 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_4, x_45, x_44);
x_47 = l_Lake_BuildMetadata_writeFile(x_5, x_46);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
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
x_51 = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(x_23, x_47, x_34);
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
x_58 = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(x_23, x_57, x_34);
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
lean_dec_ref(x_5);
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
x_103 = l_Array_extract___redArg(x_95, x_101, x_102);
x_104 = lean_box(0);
x_105 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_4, x_104, x_103);
x_106 = l_Lake_BuildMetadata_writeFile(x_5, x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
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
x_111 = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(x_23, x_110, x_94);
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
lean_dec_ref(x_5);
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
lean_dec_ref(x_5);
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
x_30 = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(x_23, x_29, x_27);
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
x_157 = l_Array_extract___redArg(x_149, x_155, x_156);
x_158 = lean_box(0);
x_159 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_4, x_158, x_157);
x_160 = l_Lake_BuildMetadata_writeFile(x_5, x_159);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
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
x_165 = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(x_136, x_164, x_147);
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
lean_dec_ref(x_5);
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
lean_dec_ref(x_5);
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
x_144 = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___lam__0(x_136, x_143, x_141);
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
lean_dec_ref(x_5);
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
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
x_14 = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_4);
return x_14;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint64_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
x_9 = lean_box_uint64(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0_spec__2(x_10, x_3);
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
x_17 = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(x_1, x_4);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_17 = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_9, x_10);
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
uint8_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; 
x_29 = lean_ctor_get_uint8(x_19, sizeof(void*)*3);
x_30 = 1;
x_31 = l_Lake_JobAction_merge(x_29, x_30);
lean_ctor_set_uint8(x_19, sizeof(void*)*3, x_31);
x_32 = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(x_15, x_1, x_6, x_7, x_8, x_9, x_19);
lean_dec_ref(x_15);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec_ref(x_32);
x_21 = x_33;
x_22 = lean_box(0);
goto block_24;
}
else
{
uint8_t x_34; 
lean_dec(x_20);
lean_dec(x_18);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
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
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_19, 0);
x_39 = lean_ctor_get_uint8(x_19, sizeof(void*)*3);
x_40 = lean_ctor_get(x_19, 1);
x_41 = lean_ctor_get(x_19, 2);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_38);
lean_dec(x_19);
x_42 = 1;
x_43 = l_Lake_JobAction_merge(x_39, x_42);
x_44 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_40);
lean_ctor_set(x_44, 2, x_41);
lean_ctor_set_uint8(x_44, sizeof(void*)*3, x_43);
x_45 = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(x_15, x_1, x_6, x_7, x_8, x_9, x_44);
lean_dec_ref(x_15);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec_ref(x_45);
x_21 = x_46;
x_22 = lean_box(0);
goto block_24;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_20);
lean_dec(x_18);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_49 = x_45;
} else {
 lean_dec_ref(x_45);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
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
lean_object* x_51; uint64_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_64; uint8_t x_65; uint8_t x_66; 
x_51 = lean_ctor_get(x_4, 0);
lean_inc(x_51);
lean_dec(x_4);
x_52 = lean_ctor_get_uint64(x_51, sizeof(void*)*3);
x_53 = lean_ctor_get(x_51, 2);
lean_inc_ref(x_53);
lean_dec_ref(x_51);
x_54 = lean_box_uint64(x_52);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(x_2, x_3, x_55, x_5, x_9, x_10);
lean_dec_ref(x_55);
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
x_64 = 0;
x_65 = lean_unbox(x_57);
x_66 = l_Lake_instDecidableEqOutputStatus(x_65, x_64);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; 
x_67 = lean_ctor_get(x_58, 0);
lean_inc_ref(x_67);
x_68 = lean_ctor_get_uint8(x_58, sizeof(void*)*3);
x_69 = lean_ctor_get(x_58, 1);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_58, 2);
lean_inc(x_70);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 lean_ctor_release(x_58, 2);
 x_71 = x_58;
} else {
 lean_dec_ref(x_58);
 x_71 = lean_box(0);
}
x_72 = 1;
x_73 = l_Lake_JobAction_merge(x_68, x_72);
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(0, 3, 1);
} else {
 x_74 = x_71;
}
lean_ctor_set(x_74, 0, x_67);
lean_ctor_set(x_74, 1, x_69);
lean_ctor_set(x_74, 2, x_70);
lean_ctor_set_uint8(x_74, sizeof(void*)*3, x_73);
x_75 = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(x_53, x_1, x_6, x_7, x_8, x_9, x_74);
lean_dec_ref(x_53);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec_ref(x_75);
x_60 = x_76;
x_61 = lean_box(0);
goto block_63;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_59);
lean_dec(x_57);
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
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
else
{
lean_dec_ref(x_53);
x_60 = x_58;
x_61 = lean_box(0);
goto block_63;
}
block_63:
{
lean_object* x_62; 
if (lean_is_scalar(x_59)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_59;
}
lean_ctor_set(x_62, 0, x_57);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
else
{
lean_object* x_81; uint8_t x_82; 
lean_dec(x_4);
x_81 = lean_ctor_get(x_9, 0);
x_82 = lean_ctor_get_uint8(x_81, sizeof(void*)*2);
if (x_82 == 0)
{
uint8_t x_83; lean_object* x_84; lean_object* x_85; 
x_83 = 0;
x_84 = lean_box(x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_10);
return x_85;
}
else
{
uint8_t x_86; 
x_86 = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(x_2, x_5);
if (x_86 == 0)
{
uint8_t x_87; lean_object* x_88; lean_object* x_89; 
x_87 = 0;
x_88 = lean_box(x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_10);
return x_89;
}
else
{
uint8_t x_90; lean_object* x_91; lean_object* x_92; 
x_90 = 1;
x_91 = lean_box(x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_10);
return x_92;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec_ref(x_50);
x_53 = lean_ctor_get(x_47, 2);
lean_inc_ref(x_47);
lean_ctor_set(x_9, 0, x_52);
x_54 = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(x_4, x_1, x_47, x_51, x_53, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; 
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
x_61 = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(x_2, x_1, x_4, x_47, x_49, x_60, x_5, x_6, x_7, x_8, x_56);
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
lean_dec_ref(x_47);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_65 = lean_ctor_get(x_54, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_54, 1);
lean_inc(x_66);
lean_dec_ref(x_54);
x_11 = x_65;
x_12 = x_66;
x_13 = lean_box(0);
goto block_15;
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec_ref(x_49);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_67 = lean_ctor_get(x_50, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_50, 1);
lean_inc(x_68);
lean_dec_ref(x_50);
lean_ctor_set(x_9, 0, x_68);
x_11 = x_67;
x_12 = x_9;
x_13 = lean_box(0);
goto block_15;
}
}
else
{
lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_69 = lean_ctor_get(x_9, 0);
x_70 = lean_ctor_get_uint8(x_9, sizeof(void*)*3);
x_71 = lean_ctor_get(x_9, 1);
x_72 = lean_ctor_get(x_9, 2);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_69);
lean_dec(x_9);
x_73 = l_Lake_buildFileUnlessUpToDate_x27___closed__0;
lean_inc_ref(x_1);
x_74 = lean_string_append(x_1, x_73);
lean_inc_ref(x_74);
x_75 = l_Lake_readTraceFile(x_74, x_69);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec_ref(x_75);
x_78 = lean_ctor_get(x_71, 2);
lean_inc_ref(x_71);
x_79 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_71);
lean_ctor_set(x_79, 2, x_72);
lean_ctor_set_uint8(x_79, sizeof(void*)*3, x_70);
x_80 = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(x_4, x_1, x_71, x_76, x_78, x_5, x_6, x_7, x_8, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec_ref(x_80);
x_83 = 0;
x_84 = lean_unbox(x_81);
lean_dec(x_81);
x_85 = l_Lake_instDecidableEqOutputStatus(x_84, x_83);
if (x_85 == 0)
{
lean_dec_ref(x_74);
lean_dec_ref(x_71);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_16 = x_82;
x_17 = lean_box(0);
goto block_44;
}
else
{
uint8_t x_86; lean_object* x_87; 
x_86 = 3;
lean_inc_ref(x_8);
lean_inc_ref(x_1);
x_87 = l_Lake_buildAction___at___00Lake_buildFileUnlessUpToDate_x27_spec__1(x_2, x_1, x_4, x_71, x_74, x_86, x_5, x_6, x_7, x_8, x_82);
lean_dec_ref(x_71);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec_ref(x_87);
x_16 = x_88;
x_17 = lean_box(0);
goto block_44;
}
else
{
lean_object* x_89; lean_object* x_90; 
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec_ref(x_87);
x_11 = x_89;
x_12 = x_90;
x_13 = lean_box(0);
goto block_15;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec_ref(x_74);
lean_dec_ref(x_71);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_91 = lean_ctor_get(x_80, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_80, 1);
lean_inc(x_92);
lean_dec_ref(x_80);
x_11 = x_91;
x_12 = x_92;
x_13 = lean_box(0);
goto block_15;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec_ref(x_74);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_93 = lean_ctor_get(x_75, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_75, 1);
lean_inc(x_94);
lean_dec_ref(x_75);
x_95 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_71);
lean_ctor_set(x_95, 2, x_72);
lean_ctor_set_uint8(x_95, sizeof(void*)*3, x_70);
x_11 = x_93;
x_12 = x_95;
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
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
x_12 = l_Lake_buildFileUnlessUpToDate_x27(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_ctor_set(x_16, 3, x_13);
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
x_13 = x_21;
x_14 = lean_box(0);
x_15 = x_19;
goto block_18;
}
else
{
lean_dec_ref(x_19);
lean_inc_ref(x_2);
x_13 = x_21;
x_14 = lean_box(0);
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
x_19 = x_23;
x_20 = lean_box(0);
x_21 = x_28;
goto block_22;
}
else
{
lean_object* x_29; 
lean_dec_ref(x_26);
x_29 = l_Lake_platformTrace___closed__4;
x_19 = x_23;
x_20 = lean_box(0);
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
lean_inc_ref(x_37);
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
x_67 = l_Lake_Hash_nil;
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
lean_ctor_set(x_74, 3, x_71);
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
x_71 = x_79;
x_72 = lean_box(0);
x_73 = x_77;
goto block_76;
}
else
{
lean_dec_ref(x_77);
lean_inc_ref(x_2);
x_71 = x_79;
x_72 = lean_box(0);
x_73 = x_2;
goto block_76;
}
}
block_101:
{
lean_object* x_84; lean_object* x_85; 
x_84 = l_Lake_joinRelative(x_82, x_83);
lean_inc_ref(x_84);
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
x_77 = x_84;
x_78 = lean_box(0);
x_79 = x_90;
goto block_80;
}
else
{
lean_object* x_91; 
lean_dec_ref(x_88);
x_91 = l_Lake_platformTrace___closed__4;
x_77 = x_84;
x_78 = lean_box(0);
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
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_cacheArtifact___redArg___lam__0(x_1);
lean_dec_ref(x_1);
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
static lean_object* _init_l_Lake_cacheArtifact___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_cacheArtifact___redArg___lam__0___boxed), 1, 0);
return x_1;
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
x_13 = l_Lake_cacheArtifact___redArg___closed__0;
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
x_14 = l_Lake_cacheArtifact___redArg___closed__0;
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
lean_inc_ref(x_57);
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
if (lean_obj_tag(x_124) == 1)
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
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
lean_free_object(x_124);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec_ref(x_128);
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
lean_dec_ref(x_129);
x_132 = l_Lake_Hash_hex(x_2);
x_133 = lean_unsigned_to_nat(0u);
x_134 = lean_string_utf8_byte_size(x_132);
lean_inc_ref(x_132);
x_135 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
lean_ctor_set(x_135, 2, x_134);
x_136 = !lean_is_exclusive(x_130);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; 
x_137 = lean_ctor_get(x_130, 0);
x_138 = lean_unsigned_to_nat(7u);
x_139 = l_String_Slice_Pos_nextn(x_135, x_133, x_138);
lean_dec_ref(x_135);
x_140 = l_Lake_getArtifacts_x3f___redArg___closed__0;
x_141 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_141, 0, x_132);
lean_ctor_set(x_141, 1, x_133);
lean_ctor_set(x_141, 2, x_139);
x_142 = l_String_Slice_toString(x_141);
lean_dec_ref(x_141);
x_143 = lean_string_append(x_140, x_142);
lean_dec_ref(x_142);
x_144 = l_Lake_getArtifacts_x3f___redArg___closed__1;
x_145 = lean_string_append(x_143, x_144);
x_146 = lean_string_append(x_145, x_131);
lean_dec(x_131);
x_147 = 2;
x_148 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set_uint8(x_148, sizeof(void*)*1, x_147);
x_149 = lean_array_push(x_137, x_148);
lean_ctor_set(x_130, 0, x_149);
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
lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_150 = lean_ctor_get(x_130, 0);
x_151 = lean_ctor_get_uint8(x_130, sizeof(void*)*3);
x_152 = lean_ctor_get(x_130, 1);
x_153 = lean_ctor_get(x_130, 2);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_150);
lean_dec(x_130);
x_154 = lean_unsigned_to_nat(7u);
x_155 = l_String_Slice_Pos_nextn(x_135, x_133, x_154);
lean_dec_ref(x_135);
x_156 = l_Lake_getArtifacts_x3f___redArg___closed__0;
x_157 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_157, 0, x_132);
lean_ctor_set(x_157, 1, x_133);
lean_ctor_set(x_157, 2, x_155);
x_158 = l_String_Slice_toString(x_157);
lean_dec_ref(x_157);
x_159 = lean_string_append(x_156, x_158);
lean_dec_ref(x_158);
x_160 = l_Lake_getArtifacts_x3f___redArg___closed__1;
x_161 = lean_string_append(x_159, x_160);
x_162 = lean_string_append(x_161, x_131);
lean_dec(x_131);
x_163 = 2;
x_164 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set_uint8(x_164, sizeof(void*)*1, x_163);
x_165 = lean_array_push(x_150, x_164);
x_166 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_152);
lean_ctor_set(x_166, 2, x_153);
lean_ctor_set_uint8(x_166, sizeof(void*)*3, x_151);
x_58 = x_6;
x_59 = x_7;
x_60 = x_8;
x_61 = x_9;
x_62 = x_10;
x_63 = x_166;
x_64 = lean_box(0);
goto block_122;
}
}
else
{
uint8_t x_167; 
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
x_167 = !lean_is_exclusive(x_128);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_128, 0);
lean_dec(x_168);
x_169 = lean_ctor_get(x_129, 0);
lean_inc(x_169);
lean_dec_ref(x_129);
lean_ctor_set(x_124, 0, x_169);
lean_ctor_set(x_128, 0, x_124);
return x_128;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_128, 1);
lean_inc(x_170);
lean_dec(x_128);
x_171 = lean_ctor_get(x_129, 0);
lean_inc(x_171);
lean_dec_ref(x_129);
lean_ctor_set(x_124, 0, x_171);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_124);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
}
}
else
{
uint8_t x_173; 
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
x_173 = !lean_is_exclusive(x_128);
if (x_173 == 0)
{
return x_128;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_128, 0);
x_175 = lean_ctor_get(x_128, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_128);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
}
else
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_124, 0);
lean_inc(x_177);
lean_dec(x_124);
lean_inc_ref(x_1);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_178 = lean_apply_8(x_1, x_177, x_6, x_7, x_8, x_9, x_10, x_53, lean_box(0));
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec_ref(x_178);
x_181 = lean_ctor_get(x_179, 0);
lean_inc(x_181);
lean_dec_ref(x_179);
x_182 = l_Lake_Hash_hex(x_2);
x_183 = lean_unsigned_to_nat(0u);
x_184 = lean_string_utf8_byte_size(x_182);
lean_inc_ref(x_182);
x_185 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
lean_ctor_set(x_185, 2, x_184);
x_186 = lean_ctor_get(x_180, 0);
lean_inc_ref(x_186);
x_187 = lean_ctor_get_uint8(x_180, sizeof(void*)*3);
x_188 = lean_ctor_get(x_180, 1);
lean_inc_ref(x_188);
x_189 = lean_ctor_get(x_180, 2);
lean_inc(x_189);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 lean_ctor_release(x_180, 2);
 x_190 = x_180;
} else {
 lean_dec_ref(x_180);
 x_190 = lean_box(0);
}
x_191 = lean_unsigned_to_nat(7u);
x_192 = l_String_Slice_Pos_nextn(x_185, x_183, x_191);
lean_dec_ref(x_185);
x_193 = l_Lake_getArtifacts_x3f___redArg___closed__0;
x_194 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_194, 0, x_182);
lean_ctor_set(x_194, 1, x_183);
lean_ctor_set(x_194, 2, x_192);
x_195 = l_String_Slice_toString(x_194);
lean_dec_ref(x_194);
x_196 = lean_string_append(x_193, x_195);
lean_dec_ref(x_195);
x_197 = l_Lake_getArtifacts_x3f___redArg___closed__1;
x_198 = lean_string_append(x_196, x_197);
x_199 = lean_string_append(x_198, x_181);
lean_dec(x_181);
x_200 = 2;
x_201 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set_uint8(x_201, sizeof(void*)*1, x_200);
x_202 = lean_array_push(x_186, x_201);
if (lean_is_scalar(x_190)) {
 x_203 = lean_alloc_ctor(0, 3, 1);
} else {
 x_203 = x_190;
}
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_188);
lean_ctor_set(x_203, 2, x_189);
lean_ctor_set_uint8(x_203, sizeof(void*)*3, x_187);
x_58 = x_6;
x_59 = x_7;
x_60 = x_8;
x_61 = x_9;
x_62 = x_10;
x_63 = x_203;
x_64 = lean_box(0);
goto block_122;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
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
x_204 = lean_ctor_get(x_178, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_205 = x_178;
} else {
 lean_dec_ref(x_178);
 x_205 = lean_box(0);
}
x_206 = lean_ctor_get(x_179, 0);
lean_inc(x_206);
lean_dec_ref(x_179);
x_207 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_207, 0, x_206);
if (lean_is_scalar(x_205)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_205;
}
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_204);
return x_208;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
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
x_209 = lean_ctor_get(x_178, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_178, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_211 = x_178;
} else {
 lean_dec_ref(x_178);
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
}
else
{
lean_dec(x_124);
x_58 = x_6;
x_59 = x_7;
x_60 = x_8;
x_61 = x_9;
x_62 = x_10;
x_63 = x_53;
x_64 = lean_box(0);
goto block_122;
}
}
else
{
uint8_t x_213; 
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
x_213 = !lean_is_exclusive(x_123);
if (x_213 == 0)
{
lean_object* x_214; 
x_214 = lean_ctor_get(x_123, 1);
lean_ctor_set(x_53, 0, x_214);
lean_ctor_set(x_123, 1, x_53);
return x_123;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_123, 0);
x_216 = lean_ctor_get(x_123, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_123);
lean_ctor_set(x_53, 0, x_216);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_53);
return x_217;
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
if (lean_obj_tag(x_67) == 1)
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
if (lean_obj_tag(x_71) == 1)
{
uint8_t x_72; 
x_72 = lean_unbox(x_54);
lean_dec(x_54);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_69);
lean_dec_ref(x_57);
lean_dec_ref(x_4);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec_ref(x_70);
x_74 = lean_ctor_get(x_71, 0);
lean_inc(x_74);
lean_dec_ref(x_71);
x_18 = x_74;
x_19 = x_73;
x_20 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_70);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_76 = lean_ctor_get(x_70, 1);
x_77 = lean_ctor_get(x_70, 0);
lean_dec(x_77);
x_78 = lean_ctor_get(x_71, 0);
lean_inc(x_78);
lean_dec_ref(x_71);
x_79 = lean_ctor_get(x_76, 0);
x_80 = lean_ctor_get_uint8(x_76, sizeof(void*)*3);
x_81 = lean_ctor_get(x_76, 1);
x_82 = lean_ctor_get(x_76, 2);
x_83 = l_Lake_Cache_writeOutputsCore(x_4, x_57, x_2, x_69);
if (lean_obj_tag(x_83) == 0)
{
lean_dec_ref(x_83);
lean_free_object(x_70);
x_18 = x_78;
x_19 = x_76;
x_20 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_84; 
lean_inc(x_82);
lean_inc_ref(x_81);
lean_inc_ref(x_79);
lean_dec(x_78);
x_84 = !lean_is_exclusive(x_76);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_85 = lean_ctor_get(x_76, 2);
lean_dec(x_85);
x_86 = lean_ctor_get(x_76, 1);
lean_dec(x_86);
x_87 = lean_ctor_get(x_76, 0);
lean_dec(x_87);
x_88 = lean_ctor_get(x_83, 0);
lean_inc(x_88);
lean_dec_ref(x_83);
x_89 = lean_io_error_to_string(x_88);
x_90 = 3;
x_91 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set_uint8(x_91, sizeof(void*)*1, x_90);
x_92 = lean_array_get_size(x_79);
x_93 = lean_array_push(x_79, x_91);
lean_ctor_set(x_76, 0, x_93);
lean_ctor_set_tag(x_70, 1);
lean_ctor_set(x_70, 0, x_92);
return x_70;
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_76);
x_94 = lean_ctor_get(x_83, 0);
lean_inc(x_94);
lean_dec_ref(x_83);
x_95 = lean_io_error_to_string(x_94);
x_96 = 3;
x_97 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set_uint8(x_97, sizeof(void*)*1, x_96);
x_98 = lean_array_get_size(x_79);
x_99 = lean_array_push(x_79, x_97);
x_100 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_81);
lean_ctor_set(x_100, 2, x_82);
lean_ctor_set_uint8(x_100, sizeof(void*)*3, x_80);
lean_ctor_set_tag(x_70, 1);
lean_ctor_set(x_70, 1, x_100);
lean_ctor_set(x_70, 0, x_98);
return x_70;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_101 = lean_ctor_get(x_70, 1);
lean_inc(x_101);
lean_dec(x_70);
x_102 = lean_ctor_get(x_71, 0);
lean_inc(x_102);
lean_dec_ref(x_71);
x_103 = lean_ctor_get(x_101, 0);
x_104 = lean_ctor_get_uint8(x_101, sizeof(void*)*3);
x_105 = lean_ctor_get(x_101, 1);
x_106 = lean_ctor_get(x_101, 2);
x_107 = l_Lake_Cache_writeOutputsCore(x_4, x_57, x_2, x_69);
if (lean_obj_tag(x_107) == 0)
{
lean_dec_ref(x_107);
x_18 = x_102;
x_19 = x_101;
x_20 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_inc(x_106);
lean_inc_ref(x_105);
lean_inc_ref(x_103);
lean_dec(x_102);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 lean_ctor_release(x_101, 2);
 x_108 = x_101;
} else {
 lean_dec_ref(x_101);
 x_108 = lean_box(0);
}
x_109 = lean_ctor_get(x_107, 0);
lean_inc(x_109);
lean_dec_ref(x_107);
x_110 = lean_io_error_to_string(x_109);
x_111 = 3;
x_112 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set_uint8(x_112, sizeof(void*)*1, x_111);
x_113 = lean_array_get_size(x_103);
x_114 = lean_array_push(x_103, x_112);
if (lean_is_scalar(x_108)) {
 x_115 = lean_alloc_ctor(0, 3, 1);
} else {
 x_115 = x_108;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_105);
lean_ctor_set(x_115, 2, x_106);
lean_ctor_set_uint8(x_115, sizeof(void*)*3, x_104);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
else
{
lean_object* x_117; 
lean_dec(x_71);
lean_dec(x_69);
lean_dec_ref(x_57);
lean_dec(x_54);
lean_dec_ref(x_4);
x_117 = lean_ctor_get(x_70, 1);
lean_inc(x_117);
lean_dec_ref(x_70);
x_13 = x_117;
x_14 = lean_box(0);
goto block_17;
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
else
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
lean_object* x_218; uint8_t x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_263; 
x_218 = lean_ctor_get(x_53, 0);
x_219 = lean_ctor_get_uint8(x_53, sizeof(void*)*3);
x_220 = lean_ctor_get(x_53, 1);
x_221 = lean_ctor_get(x_53, 2);
lean_inc(x_221);
lean_inc(x_220);
lean_inc(x_218);
lean_dec(x_53);
x_222 = l_Lake_Package_cacheScope(x_5);
lean_inc_ref(x_222);
lean_inc_ref(x_4);
x_263 = l_Lake_Cache_readOutputs_x3f(x_4, x_222, x_2, x_218);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
lean_dec_ref(x_263);
x_266 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_220);
lean_ctor_set(x_266, 2, x_221);
lean_ctor_set_uint8(x_266, sizeof(void*)*3, x_219);
if (lean_obj_tag(x_264) == 1)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_264, 0);
lean_inc(x_267);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 x_268 = x_264;
} else {
 lean_dec_ref(x_264);
 x_268 = lean_box(0);
}
lean_inc_ref(x_1);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_269 = lean_apply_8(x_1, x_267, x_6, x_7, x_8, x_9, x_10, x_266, lean_box(0));
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; 
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_268);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
lean_dec_ref(x_269);
x_272 = lean_ctor_get(x_270, 0);
lean_inc(x_272);
lean_dec_ref(x_270);
x_273 = l_Lake_Hash_hex(x_2);
x_274 = lean_unsigned_to_nat(0u);
x_275 = lean_string_utf8_byte_size(x_273);
lean_inc_ref(x_273);
x_276 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_276, 0, x_273);
lean_ctor_set(x_276, 1, x_274);
lean_ctor_set(x_276, 2, x_275);
x_277 = lean_ctor_get(x_271, 0);
lean_inc_ref(x_277);
x_278 = lean_ctor_get_uint8(x_271, sizeof(void*)*3);
x_279 = lean_ctor_get(x_271, 1);
lean_inc_ref(x_279);
x_280 = lean_ctor_get(x_271, 2);
lean_inc(x_280);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 lean_ctor_release(x_271, 2);
 x_281 = x_271;
} else {
 lean_dec_ref(x_271);
 x_281 = lean_box(0);
}
x_282 = lean_unsigned_to_nat(7u);
x_283 = l_String_Slice_Pos_nextn(x_276, x_274, x_282);
lean_dec_ref(x_276);
x_284 = l_Lake_getArtifacts_x3f___redArg___closed__0;
x_285 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_285, 0, x_273);
lean_ctor_set(x_285, 1, x_274);
lean_ctor_set(x_285, 2, x_283);
x_286 = l_String_Slice_toString(x_285);
lean_dec_ref(x_285);
x_287 = lean_string_append(x_284, x_286);
lean_dec_ref(x_286);
x_288 = l_Lake_getArtifacts_x3f___redArg___closed__1;
x_289 = lean_string_append(x_287, x_288);
x_290 = lean_string_append(x_289, x_272);
lean_dec(x_272);
x_291 = 2;
x_292 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set_uint8(x_292, sizeof(void*)*1, x_291);
x_293 = lean_array_push(x_277, x_292);
if (lean_is_scalar(x_281)) {
 x_294 = lean_alloc_ctor(0, 3, 1);
} else {
 x_294 = x_281;
}
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_279);
lean_ctor_set(x_294, 2, x_280);
lean_ctor_set_uint8(x_294, sizeof(void*)*3, x_278);
x_223 = x_6;
x_224 = x_7;
x_225 = x_8;
x_226 = x_9;
x_227 = x_10;
x_228 = x_294;
x_229 = lean_box(0);
goto block_262;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec_ref(x_222);
lean_dec(x_54);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_295 = lean_ctor_get(x_269, 1);
lean_inc(x_295);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_296 = x_269;
} else {
 lean_dec_ref(x_269);
 x_296 = lean_box(0);
}
x_297 = lean_ctor_get(x_270, 0);
lean_inc(x_297);
lean_dec_ref(x_270);
if (lean_is_scalar(x_268)) {
 x_298 = lean_alloc_ctor(1, 1, 0);
} else {
 x_298 = x_268;
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
lean_dec(x_268);
lean_dec_ref(x_222);
lean_dec(x_54);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_300 = lean_ctor_get(x_269, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_269, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_302 = x_269;
} else {
 lean_dec_ref(x_269);
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
else
{
lean_dec(x_264);
x_223 = x_6;
x_224 = x_7;
x_225 = x_8;
x_226 = x_9;
x_227 = x_10;
x_228 = x_266;
x_229 = lean_box(0);
goto block_262;
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
lean_dec_ref(x_222);
lean_dec(x_54);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_304 = lean_ctor_get(x_263, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_263, 1);
lean_inc(x_305);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_306 = x_263;
} else {
 lean_dec_ref(x_263);
 x_306 = lean_box(0);
}
x_307 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_307, 0, x_305);
lean_ctor_set(x_307, 1, x_220);
lean_ctor_set(x_307, 2, x_221);
lean_ctor_set_uint8(x_307, sizeof(void*)*3, x_219);
if (lean_is_scalar(x_306)) {
 x_308 = lean_alloc_ctor(1, 2, 0);
} else {
 x_308 = x_306;
}
lean_ctor_set(x_308, 0, x_304);
lean_ctor_set(x_308, 1, x_307);
return x_308;
}
block_262:
{
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_230; uint64_t x_231; lean_object* x_232; uint8_t x_233; 
x_230 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_230);
lean_dec_ref(x_3);
x_231 = lean_ctor_get_uint64(x_230, sizeof(void*)*3);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec_ref(x_230);
x_233 = lean_uint64_dec_eq(x_231, x_2);
if (x_233 == 0)
{
lean_dec(x_232);
lean_dec_ref(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec_ref(x_223);
lean_dec_ref(x_222);
lean_dec(x_54);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_13 = x_228;
x_14 = lean_box(0);
goto block_17;
}
else
{
if (lean_obj_tag(x_232) == 1)
{
lean_object* x_234; lean_object* x_235; 
x_234 = lean_ctor_get(x_232, 0);
lean_inc(x_234);
lean_dec_ref(x_232);
lean_inc(x_234);
x_235 = lean_apply_8(x_1, x_234, x_223, x_224, x_225, x_226, x_227, x_228, lean_box(0));
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
if (lean_obj_tag(x_236) == 1)
{
uint8_t x_237; 
x_237 = lean_unbox(x_54);
lean_dec(x_54);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; 
lean_dec(x_234);
lean_dec_ref(x_222);
lean_dec_ref(x_4);
x_238 = lean_ctor_get(x_235, 1);
lean_inc(x_238);
lean_dec_ref(x_235);
x_239 = lean_ctor_get(x_236, 0);
lean_inc(x_239);
lean_dec_ref(x_236);
x_18 = x_239;
x_19 = x_238;
x_20 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_240 = lean_ctor_get(x_235, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_241 = x_235;
} else {
 lean_dec_ref(x_235);
 x_241 = lean_box(0);
}
x_242 = lean_ctor_get(x_236, 0);
lean_inc(x_242);
lean_dec_ref(x_236);
x_243 = lean_ctor_get(x_240, 0);
x_244 = lean_ctor_get_uint8(x_240, sizeof(void*)*3);
x_245 = lean_ctor_get(x_240, 1);
x_246 = lean_ctor_get(x_240, 2);
x_247 = l_Lake_Cache_writeOutputsCore(x_4, x_222, x_2, x_234);
if (lean_obj_tag(x_247) == 0)
{
lean_dec_ref(x_247);
lean_dec(x_241);
x_18 = x_242;
x_19 = x_240;
x_20 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_inc(x_246);
lean_inc_ref(x_245);
lean_inc_ref(x_243);
lean_dec(x_242);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 lean_ctor_release(x_240, 2);
 x_248 = x_240;
} else {
 lean_dec_ref(x_240);
 x_248 = lean_box(0);
}
x_249 = lean_ctor_get(x_247, 0);
lean_inc(x_249);
lean_dec_ref(x_247);
x_250 = lean_io_error_to_string(x_249);
x_251 = 3;
x_252 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set_uint8(x_252, sizeof(void*)*1, x_251);
x_253 = lean_array_get_size(x_243);
x_254 = lean_array_push(x_243, x_252);
if (lean_is_scalar(x_248)) {
 x_255 = lean_alloc_ctor(0, 3, 1);
} else {
 x_255 = x_248;
}
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_245);
lean_ctor_set(x_255, 2, x_246);
lean_ctor_set_uint8(x_255, sizeof(void*)*3, x_244);
if (lean_is_scalar(x_241)) {
 x_256 = lean_alloc_ctor(1, 2, 0);
} else {
 x_256 = x_241;
 lean_ctor_set_tag(x_256, 1);
}
lean_ctor_set(x_256, 0, x_253);
lean_ctor_set(x_256, 1, x_255);
return x_256;
}
}
}
else
{
lean_object* x_257; 
lean_dec(x_236);
lean_dec(x_234);
lean_dec_ref(x_222);
lean_dec(x_54);
lean_dec_ref(x_4);
x_257 = lean_ctor_get(x_235, 1);
lean_inc(x_257);
lean_dec_ref(x_235);
x_13 = x_257;
x_14 = lean_box(0);
goto block_17;
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_234);
lean_dec_ref(x_222);
lean_dec(x_54);
lean_dec_ref(x_4);
x_258 = lean_ctor_get(x_235, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_235, 1);
lean_inc(x_259);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_260 = x_235;
} else {
 lean_dec_ref(x_235);
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
else
{
lean_dec(x_232);
lean_dec_ref(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec_ref(x_223);
lean_dec_ref(x_222);
lean_dec(x_54);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_13 = x_228;
x_14 = lean_box(0);
goto block_17;
}
}
}
else
{
lean_dec_ref(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec_ref(x_223);
lean_dec_ref(x_222);
lean_dec(x_54);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_13 = x_228;
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
lean_inc_ref(x_329);
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
if (lean_obj_tag(x_371) == 1)
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
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
lean_dec(x_375);
x_378 = lean_ctor_get(x_376, 1);
lean_inc(x_378);
lean_dec_ref(x_376);
x_379 = lean_ctor_get(x_377, 0);
lean_inc(x_379);
lean_dec_ref(x_377);
x_380 = l_Lake_Hash_hex(x_2);
x_381 = lean_unsigned_to_nat(0u);
x_382 = lean_string_utf8_byte_size(x_380);
lean_inc_ref(x_380);
x_383 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_383, 0, x_380);
lean_ctor_set(x_383, 1, x_381);
lean_ctor_set(x_383, 2, x_382);
x_384 = lean_ctor_get(x_378, 0);
lean_inc_ref(x_384);
x_385 = lean_ctor_get_uint8(x_378, sizeof(void*)*3);
x_386 = lean_ctor_get(x_378, 1);
lean_inc_ref(x_386);
x_387 = lean_ctor_get(x_378, 2);
lean_inc(x_387);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 lean_ctor_release(x_378, 2);
 x_388 = x_378;
} else {
 lean_dec_ref(x_378);
 x_388 = lean_box(0);
}
x_389 = lean_unsigned_to_nat(7u);
x_390 = l_String_Slice_Pos_nextn(x_383, x_381, x_389);
lean_dec_ref(x_383);
x_391 = l_Lake_getArtifacts_x3f___redArg___closed__0;
x_392 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_392, 0, x_380);
lean_ctor_set(x_392, 1, x_381);
lean_ctor_set(x_392, 2, x_390);
x_393 = l_String_Slice_toString(x_392);
lean_dec_ref(x_392);
x_394 = lean_string_append(x_391, x_393);
lean_dec_ref(x_393);
x_395 = l_Lake_getArtifacts_x3f___redArg___closed__1;
x_396 = lean_string_append(x_394, x_395);
x_397 = lean_string_append(x_396, x_379);
lean_dec(x_379);
x_398 = 2;
x_399 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_399, 0, x_397);
lean_ctor_set_uint8(x_399, sizeof(void*)*1, x_398);
x_400 = lean_array_push(x_384, x_399);
if (lean_is_scalar(x_388)) {
 x_401 = lean_alloc_ctor(0, 3, 1);
} else {
 x_401 = x_388;
}
lean_ctor_set(x_401, 0, x_400);
lean_ctor_set(x_401, 1, x_386);
lean_ctor_set(x_401, 2, x_387);
lean_ctor_set_uint8(x_401, sizeof(void*)*3, x_385);
x_330 = x_6;
x_331 = x_7;
x_332 = x_8;
x_333 = x_9;
x_334 = x_10;
x_335 = x_401;
x_336 = lean_box(0);
goto block_369;
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
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
x_402 = lean_ctor_get(x_376, 1);
lean_inc(x_402);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 x_403 = x_376;
} else {
 lean_dec_ref(x_376);
 x_403 = lean_box(0);
}
x_404 = lean_ctor_get(x_377, 0);
lean_inc(x_404);
lean_dec_ref(x_377);
if (lean_is_scalar(x_375)) {
 x_405 = lean_alloc_ctor(1, 1, 0);
} else {
 x_405 = x_375;
}
lean_ctor_set(x_405, 0, x_404);
if (lean_is_scalar(x_403)) {
 x_406 = lean_alloc_ctor(0, 2, 0);
} else {
 x_406 = x_403;
}
lean_ctor_set(x_406, 0, x_405);
lean_ctor_set(x_406, 1, x_402);
return x_406;
}
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
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
x_407 = lean_ctor_get(x_376, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_376, 1);
lean_inc(x_408);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 x_409 = x_376;
} else {
 lean_dec_ref(x_376);
 x_409 = lean_box(0);
}
if (lean_is_scalar(x_409)) {
 x_410 = lean_alloc_ctor(1, 2, 0);
} else {
 x_410 = x_409;
}
lean_ctor_set(x_410, 0, x_407);
lean_ctor_set(x_410, 1, x_408);
return x_410;
}
}
else
{
lean_dec(x_371);
x_330 = x_6;
x_331 = x_7;
x_332 = x_8;
x_333 = x_9;
x_334 = x_10;
x_335 = x_373;
x_336 = lean_box(0);
goto block_369;
}
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
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
x_411 = lean_ctor_get(x_370, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_370, 1);
lean_inc(x_412);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 x_413 = x_370;
} else {
 lean_dec_ref(x_370);
 x_413 = lean_box(0);
}
if (lean_is_scalar(x_328)) {
 x_414 = lean_alloc_ctor(0, 3, 1);
} else {
 x_414 = x_328;
}
lean_ctor_set(x_414, 0, x_412);
lean_ctor_set(x_414, 1, x_326);
lean_ctor_set(x_414, 2, x_327);
lean_ctor_set_uint8(x_414, sizeof(void*)*3, x_325);
if (lean_is_scalar(x_413)) {
 x_415 = lean_alloc_ctor(1, 2, 0);
} else {
 x_415 = x_413;
}
lean_ctor_set(x_415, 0, x_411);
lean_ctor_set(x_415, 1, x_414);
return x_415;
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
if (lean_obj_tag(x_339) == 1)
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
if (lean_obj_tag(x_343) == 1)
{
uint8_t x_344; 
x_344 = lean_unbox(x_323);
lean_dec(x_323);
if (x_344 == 0)
{
lean_object* x_345; lean_object* x_346; 
lean_dec(x_341);
lean_dec_ref(x_329);
lean_dec_ref(x_4);
x_345 = lean_ctor_get(x_342, 1);
lean_inc(x_345);
lean_dec_ref(x_342);
x_346 = lean_ctor_get(x_343, 0);
lean_inc(x_346);
lean_dec_ref(x_343);
x_18 = x_346;
x_19 = x_345;
x_20 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; uint8_t x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_347 = lean_ctor_get(x_342, 1);
lean_inc(x_347);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_348 = x_342;
} else {
 lean_dec_ref(x_342);
 x_348 = lean_box(0);
}
x_349 = lean_ctor_get(x_343, 0);
lean_inc(x_349);
lean_dec_ref(x_343);
x_350 = lean_ctor_get(x_347, 0);
x_351 = lean_ctor_get_uint8(x_347, sizeof(void*)*3);
x_352 = lean_ctor_get(x_347, 1);
x_353 = lean_ctor_get(x_347, 2);
x_354 = l_Lake_Cache_writeOutputsCore(x_4, x_329, x_2, x_341);
if (lean_obj_tag(x_354) == 0)
{
lean_dec_ref(x_354);
lean_dec(x_348);
x_18 = x_349;
x_19 = x_347;
x_20 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; uint8_t x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
lean_inc(x_353);
lean_inc_ref(x_352);
lean_inc_ref(x_350);
lean_dec(x_349);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 x_355 = x_347;
} else {
 lean_dec_ref(x_347);
 x_355 = lean_box(0);
}
x_356 = lean_ctor_get(x_354, 0);
lean_inc(x_356);
lean_dec_ref(x_354);
x_357 = lean_io_error_to_string(x_356);
x_358 = 3;
x_359 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_359, 0, x_357);
lean_ctor_set_uint8(x_359, sizeof(void*)*1, x_358);
x_360 = lean_array_get_size(x_350);
x_361 = lean_array_push(x_350, x_359);
if (lean_is_scalar(x_355)) {
 x_362 = lean_alloc_ctor(0, 3, 1);
} else {
 x_362 = x_355;
}
lean_ctor_set(x_362, 0, x_361);
lean_ctor_set(x_362, 1, x_352);
lean_ctor_set(x_362, 2, x_353);
lean_ctor_set_uint8(x_362, sizeof(void*)*3, x_351);
if (lean_is_scalar(x_348)) {
 x_363 = lean_alloc_ctor(1, 2, 0);
} else {
 x_363 = x_348;
 lean_ctor_set_tag(x_363, 1);
}
lean_ctor_set(x_363, 0, x_360);
lean_ctor_set(x_363, 1, x_362);
return x_363;
}
}
}
else
{
lean_object* x_364; 
lean_dec(x_343);
lean_dec(x_341);
lean_dec_ref(x_329);
lean_dec(x_323);
lean_dec_ref(x_4);
x_364 = lean_ctor_get(x_342, 1);
lean_inc(x_364);
lean_dec_ref(x_342);
x_13 = x_364;
x_14 = lean_box(0);
goto block_17;
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
else
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
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_416 = lean_ctor_get(x_321, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_321, 1);
lean_inc(x_417);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 x_418 = x_321;
} else {
 lean_dec_ref(x_321);
 x_418 = lean_box(0);
}
if (lean_is_scalar(x_418)) {
 x_419 = lean_alloc_ctor(1, 2, 0);
} else {
 x_419 = x_418;
}
lean_ctor_set(x_419, 0, x_416);
lean_ctor_set(x_419, 1, x_417);
return x_419;
}
}
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_420 = lean_ctor_get(x_24, 1);
x_421 = lean_ctor_get(x_26, 0);
x_422 = lean_ctor_get(x_26, 1);
lean_inc(x_422);
lean_inc(x_421);
lean_dec(x_26);
lean_inc(x_420);
lean_inc(x_422);
x_423 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_423, 0, x_422);
lean_closure_set(x_423, 1, x_420);
lean_inc(x_420);
lean_inc(x_422);
x_424 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_424, 0, x_422);
lean_closure_set(x_424, 1, x_420);
lean_inc_ref(x_423);
lean_inc(x_422);
x_425 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_425, 0, x_422);
lean_closure_set(x_425, 1, x_423);
lean_inc(x_422);
lean_inc_ref(x_421);
x_426 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_426, 0, x_421);
lean_closure_set(x_426, 1, x_422);
lean_closure_set(x_426, 2, x_420);
x_427 = l_Lake_EStateT_instFunctor___redArg(x_421);
x_428 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_428, 0, x_422);
x_429 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_429, 0, x_427);
lean_ctor_set(x_429, 1, x_428);
lean_ctor_set(x_429, 2, x_426);
lean_ctor_set(x_429, 3, x_425);
lean_ctor_set(x_429, 4, x_424);
lean_ctor_set(x_24, 1, x_423);
lean_ctor_set(x_24, 0, x_429);
x_430 = l_ReaderT_instMonad___redArg(x_24);
x_431 = l_ReaderT_instMonad___redArg(x_430);
x_432 = l_ReaderT_instMonad___redArg(x_431);
x_433 = lean_ctor_get(x_432, 0);
lean_inc_ref(x_433);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 x_434 = x_432;
} else {
 lean_dec_ref(x_432);
 x_434 = lean_box(0);
}
x_435 = lean_ctor_get(x_433, 0);
lean_inc_ref(x_435);
lean_dec_ref(x_433);
lean_inc_ref(x_435);
x_436 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_436, 0, x_435);
x_437 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_437, 0, x_435);
if (lean_is_scalar(x_434)) {
 x_438 = lean_alloc_ctor(0, 2, 0);
} else {
 x_438 = x_434;
}
lean_ctor_set(x_438, 0, x_436);
lean_ctor_set(x_438, 1, x_437);
x_439 = l_Lake_EquipT_instFunctor___redArg(x_438);
x_440 = l_Lake_instMonadWorkspaceJobM;
lean_inc_ref(x_5);
x_441 = l_Lake_Package_isArtifactCacheEnabled___redArg(x_439, x_440, x_5);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_442 = lean_apply_7(x_441, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_442) == 0)
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; uint8_t x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_491; 
x_443 = lean_ctor_get(x_442, 1);
lean_inc(x_443);
x_444 = lean_ctor_get(x_442, 0);
lean_inc(x_444);
lean_dec_ref(x_442);
x_445 = lean_ctor_get(x_443, 0);
lean_inc_ref(x_445);
x_446 = lean_ctor_get_uint8(x_443, sizeof(void*)*3);
x_447 = lean_ctor_get(x_443, 1);
lean_inc_ref(x_447);
x_448 = lean_ctor_get(x_443, 2);
lean_inc(x_448);
if (lean_is_exclusive(x_443)) {
 lean_ctor_release(x_443, 0);
 lean_ctor_release(x_443, 1);
 lean_ctor_release(x_443, 2);
 x_449 = x_443;
} else {
 lean_dec_ref(x_443);
 x_449 = lean_box(0);
}
x_450 = l_Lake_Package_cacheScope(x_5);
lean_inc_ref(x_450);
lean_inc_ref(x_4);
x_491 = l_Lake_Cache_readOutputs_x3f(x_4, x_450, x_2, x_445);
if (lean_obj_tag(x_491) == 0)
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_492 = lean_ctor_get(x_491, 0);
lean_inc(x_492);
x_493 = lean_ctor_get(x_491, 1);
lean_inc(x_493);
lean_dec_ref(x_491);
if (lean_is_scalar(x_449)) {
 x_494 = lean_alloc_ctor(0, 3, 1);
} else {
 x_494 = x_449;
}
lean_ctor_set(x_494, 0, x_493);
lean_ctor_set(x_494, 1, x_447);
lean_ctor_set(x_494, 2, x_448);
lean_ctor_set_uint8(x_494, sizeof(void*)*3, x_446);
if (lean_obj_tag(x_492) == 1)
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; 
x_495 = lean_ctor_get(x_492, 0);
lean_inc(x_495);
if (lean_is_exclusive(x_492)) {
 lean_ctor_release(x_492, 0);
 x_496 = x_492;
} else {
 lean_dec_ref(x_492);
 x_496 = lean_box(0);
}
lean_inc_ref(x_1);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_497 = lean_apply_8(x_1, x_495, x_6, x_7, x_8, x_9, x_10, x_494, lean_box(0));
if (lean_obj_tag(x_497) == 0)
{
lean_object* x_498; 
x_498 = lean_ctor_get(x_497, 0);
lean_inc(x_498);
if (lean_obj_tag(x_498) == 0)
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; uint8_t x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; uint8_t x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; 
lean_dec(x_496);
x_499 = lean_ctor_get(x_497, 1);
lean_inc(x_499);
lean_dec_ref(x_497);
x_500 = lean_ctor_get(x_498, 0);
lean_inc(x_500);
lean_dec_ref(x_498);
x_501 = l_Lake_Hash_hex(x_2);
x_502 = lean_unsigned_to_nat(0u);
x_503 = lean_string_utf8_byte_size(x_501);
lean_inc_ref(x_501);
x_504 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_504, 0, x_501);
lean_ctor_set(x_504, 1, x_502);
lean_ctor_set(x_504, 2, x_503);
x_505 = lean_ctor_get(x_499, 0);
lean_inc_ref(x_505);
x_506 = lean_ctor_get_uint8(x_499, sizeof(void*)*3);
x_507 = lean_ctor_get(x_499, 1);
lean_inc_ref(x_507);
x_508 = lean_ctor_get(x_499, 2);
lean_inc(x_508);
if (lean_is_exclusive(x_499)) {
 lean_ctor_release(x_499, 0);
 lean_ctor_release(x_499, 1);
 lean_ctor_release(x_499, 2);
 x_509 = x_499;
} else {
 lean_dec_ref(x_499);
 x_509 = lean_box(0);
}
x_510 = lean_unsigned_to_nat(7u);
x_511 = l_String_Slice_Pos_nextn(x_504, x_502, x_510);
lean_dec_ref(x_504);
x_512 = l_Lake_getArtifacts_x3f___redArg___closed__0;
x_513 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_513, 0, x_501);
lean_ctor_set(x_513, 1, x_502);
lean_ctor_set(x_513, 2, x_511);
x_514 = l_String_Slice_toString(x_513);
lean_dec_ref(x_513);
x_515 = lean_string_append(x_512, x_514);
lean_dec_ref(x_514);
x_516 = l_Lake_getArtifacts_x3f___redArg___closed__1;
x_517 = lean_string_append(x_515, x_516);
x_518 = lean_string_append(x_517, x_500);
lean_dec(x_500);
x_519 = 2;
x_520 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_520, 0, x_518);
lean_ctor_set_uint8(x_520, sizeof(void*)*1, x_519);
x_521 = lean_array_push(x_505, x_520);
if (lean_is_scalar(x_509)) {
 x_522 = lean_alloc_ctor(0, 3, 1);
} else {
 x_522 = x_509;
}
lean_ctor_set(x_522, 0, x_521);
lean_ctor_set(x_522, 1, x_507);
lean_ctor_set(x_522, 2, x_508);
lean_ctor_set_uint8(x_522, sizeof(void*)*3, x_506);
x_451 = x_6;
x_452 = x_7;
x_453 = x_8;
x_454 = x_9;
x_455 = x_10;
x_456 = x_522;
x_457 = lean_box(0);
goto block_490;
}
else
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; 
lean_dec_ref(x_450);
lean_dec(x_444);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_523 = lean_ctor_get(x_497, 1);
lean_inc(x_523);
if (lean_is_exclusive(x_497)) {
 lean_ctor_release(x_497, 0);
 lean_ctor_release(x_497, 1);
 x_524 = x_497;
} else {
 lean_dec_ref(x_497);
 x_524 = lean_box(0);
}
x_525 = lean_ctor_get(x_498, 0);
lean_inc(x_525);
lean_dec_ref(x_498);
if (lean_is_scalar(x_496)) {
 x_526 = lean_alloc_ctor(1, 1, 0);
} else {
 x_526 = x_496;
}
lean_ctor_set(x_526, 0, x_525);
if (lean_is_scalar(x_524)) {
 x_527 = lean_alloc_ctor(0, 2, 0);
} else {
 x_527 = x_524;
}
lean_ctor_set(x_527, 0, x_526);
lean_ctor_set(x_527, 1, x_523);
return x_527;
}
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; 
lean_dec(x_496);
lean_dec_ref(x_450);
lean_dec(x_444);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_528 = lean_ctor_get(x_497, 0);
lean_inc(x_528);
x_529 = lean_ctor_get(x_497, 1);
lean_inc(x_529);
if (lean_is_exclusive(x_497)) {
 lean_ctor_release(x_497, 0);
 lean_ctor_release(x_497, 1);
 x_530 = x_497;
} else {
 lean_dec_ref(x_497);
 x_530 = lean_box(0);
}
if (lean_is_scalar(x_530)) {
 x_531 = lean_alloc_ctor(1, 2, 0);
} else {
 x_531 = x_530;
}
lean_ctor_set(x_531, 0, x_528);
lean_ctor_set(x_531, 1, x_529);
return x_531;
}
}
else
{
lean_dec(x_492);
x_451 = x_6;
x_452 = x_7;
x_453 = x_8;
x_454 = x_9;
x_455 = x_10;
x_456 = x_494;
x_457 = lean_box(0);
goto block_490;
}
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; 
lean_dec_ref(x_450);
lean_dec(x_444);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_532 = lean_ctor_get(x_491, 0);
lean_inc(x_532);
x_533 = lean_ctor_get(x_491, 1);
lean_inc(x_533);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 lean_ctor_release(x_491, 1);
 x_534 = x_491;
} else {
 lean_dec_ref(x_491);
 x_534 = lean_box(0);
}
if (lean_is_scalar(x_449)) {
 x_535 = lean_alloc_ctor(0, 3, 1);
} else {
 x_535 = x_449;
}
lean_ctor_set(x_535, 0, x_533);
lean_ctor_set(x_535, 1, x_447);
lean_ctor_set(x_535, 2, x_448);
lean_ctor_set_uint8(x_535, sizeof(void*)*3, x_446);
if (lean_is_scalar(x_534)) {
 x_536 = lean_alloc_ctor(1, 2, 0);
} else {
 x_536 = x_534;
}
lean_ctor_set(x_536, 0, x_532);
lean_ctor_set(x_536, 1, x_535);
return x_536;
}
block_490:
{
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_458; uint64_t x_459; lean_object* x_460; uint8_t x_461; 
x_458 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_458);
lean_dec_ref(x_3);
x_459 = lean_ctor_get_uint64(x_458, sizeof(void*)*3);
x_460 = lean_ctor_get(x_458, 1);
lean_inc(x_460);
lean_dec_ref(x_458);
x_461 = lean_uint64_dec_eq(x_459, x_2);
if (x_461 == 0)
{
lean_dec(x_460);
lean_dec_ref(x_455);
lean_dec(x_454);
lean_dec(x_453);
lean_dec(x_452);
lean_dec_ref(x_451);
lean_dec_ref(x_450);
lean_dec(x_444);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_13 = x_456;
x_14 = lean_box(0);
goto block_17;
}
else
{
if (lean_obj_tag(x_460) == 1)
{
lean_object* x_462; lean_object* x_463; 
x_462 = lean_ctor_get(x_460, 0);
lean_inc(x_462);
lean_dec_ref(x_460);
lean_inc(x_462);
x_463 = lean_apply_8(x_1, x_462, x_451, x_452, x_453, x_454, x_455, x_456, lean_box(0));
if (lean_obj_tag(x_463) == 0)
{
lean_object* x_464; 
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
if (lean_obj_tag(x_464) == 1)
{
uint8_t x_465; 
x_465 = lean_unbox(x_444);
lean_dec(x_444);
if (x_465 == 0)
{
lean_object* x_466; lean_object* x_467; 
lean_dec(x_462);
lean_dec_ref(x_450);
lean_dec_ref(x_4);
x_466 = lean_ctor_get(x_463, 1);
lean_inc(x_466);
lean_dec_ref(x_463);
x_467 = lean_ctor_get(x_464, 0);
lean_inc(x_467);
lean_dec_ref(x_464);
x_18 = x_467;
x_19 = x_466;
x_20 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; uint8_t x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_468 = lean_ctor_get(x_463, 1);
lean_inc(x_468);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 x_469 = x_463;
} else {
 lean_dec_ref(x_463);
 x_469 = lean_box(0);
}
x_470 = lean_ctor_get(x_464, 0);
lean_inc(x_470);
lean_dec_ref(x_464);
x_471 = lean_ctor_get(x_468, 0);
x_472 = lean_ctor_get_uint8(x_468, sizeof(void*)*3);
x_473 = lean_ctor_get(x_468, 1);
x_474 = lean_ctor_get(x_468, 2);
x_475 = l_Lake_Cache_writeOutputsCore(x_4, x_450, x_2, x_462);
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
else
{
lean_object* x_485; 
lean_dec(x_464);
lean_dec(x_462);
lean_dec_ref(x_450);
lean_dec(x_444);
lean_dec_ref(x_4);
x_485 = lean_ctor_get(x_463, 1);
lean_inc(x_485);
lean_dec_ref(x_463);
x_13 = x_485;
x_14 = lean_box(0);
goto block_17;
}
}
else
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; 
lean_dec(x_462);
lean_dec_ref(x_450);
lean_dec(x_444);
lean_dec_ref(x_4);
x_486 = lean_ctor_get(x_463, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_463, 1);
lean_inc(x_487);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 x_488 = x_463;
} else {
 lean_dec_ref(x_463);
 x_488 = lean_box(0);
}
if (lean_is_scalar(x_488)) {
 x_489 = lean_alloc_ctor(1, 2, 0);
} else {
 x_489 = x_488;
}
lean_ctor_set(x_489, 0, x_486);
lean_ctor_set(x_489, 1, x_487);
return x_489;
}
}
else
{
lean_dec(x_460);
lean_dec_ref(x_455);
lean_dec(x_454);
lean_dec(x_453);
lean_dec(x_452);
lean_dec_ref(x_451);
lean_dec_ref(x_450);
lean_dec(x_444);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_13 = x_456;
x_14 = lean_box(0);
goto block_17;
}
}
}
else
{
lean_dec_ref(x_455);
lean_dec(x_454);
lean_dec(x_453);
lean_dec(x_452);
lean_dec_ref(x_451);
lean_dec_ref(x_450);
lean_dec(x_444);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_13 = x_456;
x_14 = lean_box(0);
goto block_17;
}
}
}
else
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_537 = lean_ctor_get(x_442, 0);
lean_inc(x_537);
x_538 = lean_ctor_get(x_442, 1);
lean_inc(x_538);
if (lean_is_exclusive(x_442)) {
 lean_ctor_release(x_442, 0);
 lean_ctor_release(x_442, 1);
 x_539 = x_442;
} else {
 lean_dec_ref(x_442);
 x_539 = lean_box(0);
}
if (lean_is_scalar(x_539)) {
 x_540 = lean_alloc_ctor(1, 2, 0);
} else {
 x_540 = x_539;
}
lean_ctor_set(x_540, 0, x_537);
lean_ctor_set(x_540, 1, x_538);
return x_540;
}
}
}
else
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; 
x_541 = lean_ctor_get(x_24, 0);
x_542 = lean_ctor_get(x_24, 1);
lean_inc(x_542);
lean_inc(x_541);
lean_dec(x_24);
x_543 = lean_ctor_get(x_541, 0);
lean_inc_ref(x_543);
x_544 = lean_ctor_get(x_541, 1);
lean_inc(x_544);
if (lean_is_exclusive(x_541)) {
 lean_ctor_release(x_541, 0);
 lean_ctor_release(x_541, 1);
 lean_ctor_release(x_541, 2);
 lean_ctor_release(x_541, 3);
 lean_ctor_release(x_541, 4);
 x_545 = x_541;
} else {
 lean_dec_ref(x_541);
 x_545 = lean_box(0);
}
lean_inc(x_542);
lean_inc(x_544);
x_546 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_546, 0, x_544);
lean_closure_set(x_546, 1, x_542);
lean_inc(x_542);
lean_inc(x_544);
x_547 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_547, 0, x_544);
lean_closure_set(x_547, 1, x_542);
lean_inc_ref(x_546);
lean_inc(x_544);
x_548 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_548, 0, x_544);
lean_closure_set(x_548, 1, x_546);
lean_inc(x_544);
lean_inc_ref(x_543);
x_549 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_549, 0, x_543);
lean_closure_set(x_549, 1, x_544);
lean_closure_set(x_549, 2, x_542);
x_550 = l_Lake_EStateT_instFunctor___redArg(x_543);
x_551 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_551, 0, x_544);
if (lean_is_scalar(x_545)) {
 x_552 = lean_alloc_ctor(0, 5, 0);
} else {
 x_552 = x_545;
}
lean_ctor_set(x_552, 0, x_550);
lean_ctor_set(x_552, 1, x_551);
lean_ctor_set(x_552, 2, x_549);
lean_ctor_set(x_552, 3, x_548);
lean_ctor_set(x_552, 4, x_547);
x_553 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_553, 0, x_552);
lean_ctor_set(x_553, 1, x_546);
x_554 = l_ReaderT_instMonad___redArg(x_553);
x_555 = l_ReaderT_instMonad___redArg(x_554);
x_556 = l_ReaderT_instMonad___redArg(x_555);
x_557 = lean_ctor_get(x_556, 0);
lean_inc_ref(x_557);
if (lean_is_exclusive(x_556)) {
 lean_ctor_release(x_556, 0);
 lean_ctor_release(x_556, 1);
 x_558 = x_556;
} else {
 lean_dec_ref(x_556);
 x_558 = lean_box(0);
}
x_559 = lean_ctor_get(x_557, 0);
lean_inc_ref(x_559);
lean_dec_ref(x_557);
lean_inc_ref(x_559);
x_560 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_560, 0, x_559);
x_561 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_561, 0, x_559);
if (lean_is_scalar(x_558)) {
 x_562 = lean_alloc_ctor(0, 2, 0);
} else {
 x_562 = x_558;
}
lean_ctor_set(x_562, 0, x_560);
lean_ctor_set(x_562, 1, x_561);
x_563 = l_Lake_EquipT_instFunctor___redArg(x_562);
x_564 = l_Lake_instMonadWorkspaceJobM;
lean_inc_ref(x_5);
x_565 = l_Lake_Package_isArtifactCacheEnabled___redArg(x_563, x_564, x_5);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_566 = lean_apply_7(x_565, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_566) == 0)
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; uint8_t x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_615; 
x_567 = lean_ctor_get(x_566, 1);
lean_inc(x_567);
x_568 = lean_ctor_get(x_566, 0);
lean_inc(x_568);
lean_dec_ref(x_566);
x_569 = lean_ctor_get(x_567, 0);
lean_inc_ref(x_569);
x_570 = lean_ctor_get_uint8(x_567, sizeof(void*)*3);
x_571 = lean_ctor_get(x_567, 1);
lean_inc_ref(x_571);
x_572 = lean_ctor_get(x_567, 2);
lean_inc(x_572);
if (lean_is_exclusive(x_567)) {
 lean_ctor_release(x_567, 0);
 lean_ctor_release(x_567, 1);
 lean_ctor_release(x_567, 2);
 x_573 = x_567;
} else {
 lean_dec_ref(x_567);
 x_573 = lean_box(0);
}
x_574 = l_Lake_Package_cacheScope(x_5);
lean_inc_ref(x_574);
lean_inc_ref(x_4);
x_615 = l_Lake_Cache_readOutputs_x3f(x_4, x_574, x_2, x_569);
if (lean_obj_tag(x_615) == 0)
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; 
x_616 = lean_ctor_get(x_615, 0);
lean_inc(x_616);
x_617 = lean_ctor_get(x_615, 1);
lean_inc(x_617);
lean_dec_ref(x_615);
if (lean_is_scalar(x_573)) {
 x_618 = lean_alloc_ctor(0, 3, 1);
} else {
 x_618 = x_573;
}
lean_ctor_set(x_618, 0, x_617);
lean_ctor_set(x_618, 1, x_571);
lean_ctor_set(x_618, 2, x_572);
lean_ctor_set_uint8(x_618, sizeof(void*)*3, x_570);
if (lean_obj_tag(x_616) == 1)
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; 
x_619 = lean_ctor_get(x_616, 0);
lean_inc(x_619);
if (lean_is_exclusive(x_616)) {
 lean_ctor_release(x_616, 0);
 x_620 = x_616;
} else {
 lean_dec_ref(x_616);
 x_620 = lean_box(0);
}
lean_inc_ref(x_1);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_621 = lean_apply_8(x_1, x_619, x_6, x_7, x_8, x_9, x_10, x_618, lean_box(0));
if (lean_obj_tag(x_621) == 0)
{
lean_object* x_622; 
x_622 = lean_ctor_get(x_621, 0);
lean_inc(x_622);
if (lean_obj_tag(x_622) == 0)
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; uint8_t x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; uint8_t x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; 
lean_dec(x_620);
x_623 = lean_ctor_get(x_621, 1);
lean_inc(x_623);
lean_dec_ref(x_621);
x_624 = lean_ctor_get(x_622, 0);
lean_inc(x_624);
lean_dec_ref(x_622);
x_625 = l_Lake_Hash_hex(x_2);
x_626 = lean_unsigned_to_nat(0u);
x_627 = lean_string_utf8_byte_size(x_625);
lean_inc_ref(x_625);
x_628 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_628, 0, x_625);
lean_ctor_set(x_628, 1, x_626);
lean_ctor_set(x_628, 2, x_627);
x_629 = lean_ctor_get(x_623, 0);
lean_inc_ref(x_629);
x_630 = lean_ctor_get_uint8(x_623, sizeof(void*)*3);
x_631 = lean_ctor_get(x_623, 1);
lean_inc_ref(x_631);
x_632 = lean_ctor_get(x_623, 2);
lean_inc(x_632);
if (lean_is_exclusive(x_623)) {
 lean_ctor_release(x_623, 0);
 lean_ctor_release(x_623, 1);
 lean_ctor_release(x_623, 2);
 x_633 = x_623;
} else {
 lean_dec_ref(x_623);
 x_633 = lean_box(0);
}
x_634 = lean_unsigned_to_nat(7u);
x_635 = l_String_Slice_Pos_nextn(x_628, x_626, x_634);
lean_dec_ref(x_628);
x_636 = l_Lake_getArtifacts_x3f___redArg___closed__0;
x_637 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_637, 0, x_625);
lean_ctor_set(x_637, 1, x_626);
lean_ctor_set(x_637, 2, x_635);
x_638 = l_String_Slice_toString(x_637);
lean_dec_ref(x_637);
x_639 = lean_string_append(x_636, x_638);
lean_dec_ref(x_638);
x_640 = l_Lake_getArtifacts_x3f___redArg___closed__1;
x_641 = lean_string_append(x_639, x_640);
x_642 = lean_string_append(x_641, x_624);
lean_dec(x_624);
x_643 = 2;
x_644 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_644, 0, x_642);
lean_ctor_set_uint8(x_644, sizeof(void*)*1, x_643);
x_645 = lean_array_push(x_629, x_644);
if (lean_is_scalar(x_633)) {
 x_646 = lean_alloc_ctor(0, 3, 1);
} else {
 x_646 = x_633;
}
lean_ctor_set(x_646, 0, x_645);
lean_ctor_set(x_646, 1, x_631);
lean_ctor_set(x_646, 2, x_632);
lean_ctor_set_uint8(x_646, sizeof(void*)*3, x_630);
x_575 = x_6;
x_576 = x_7;
x_577 = x_8;
x_578 = x_9;
x_579 = x_10;
x_580 = x_646;
x_581 = lean_box(0);
goto block_614;
}
else
{
lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; 
lean_dec_ref(x_574);
lean_dec(x_568);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_647 = lean_ctor_get(x_621, 1);
lean_inc(x_647);
if (lean_is_exclusive(x_621)) {
 lean_ctor_release(x_621, 0);
 lean_ctor_release(x_621, 1);
 x_648 = x_621;
} else {
 lean_dec_ref(x_621);
 x_648 = lean_box(0);
}
x_649 = lean_ctor_get(x_622, 0);
lean_inc(x_649);
lean_dec_ref(x_622);
if (lean_is_scalar(x_620)) {
 x_650 = lean_alloc_ctor(1, 1, 0);
} else {
 x_650 = x_620;
}
lean_ctor_set(x_650, 0, x_649);
if (lean_is_scalar(x_648)) {
 x_651 = lean_alloc_ctor(0, 2, 0);
} else {
 x_651 = x_648;
}
lean_ctor_set(x_651, 0, x_650);
lean_ctor_set(x_651, 1, x_647);
return x_651;
}
}
else
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; 
lean_dec(x_620);
lean_dec_ref(x_574);
lean_dec(x_568);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_652 = lean_ctor_get(x_621, 0);
lean_inc(x_652);
x_653 = lean_ctor_get(x_621, 1);
lean_inc(x_653);
if (lean_is_exclusive(x_621)) {
 lean_ctor_release(x_621, 0);
 lean_ctor_release(x_621, 1);
 x_654 = x_621;
} else {
 lean_dec_ref(x_621);
 x_654 = lean_box(0);
}
if (lean_is_scalar(x_654)) {
 x_655 = lean_alloc_ctor(1, 2, 0);
} else {
 x_655 = x_654;
}
lean_ctor_set(x_655, 0, x_652);
lean_ctor_set(x_655, 1, x_653);
return x_655;
}
}
else
{
lean_dec(x_616);
x_575 = x_6;
x_576 = x_7;
x_577 = x_8;
x_578 = x_9;
x_579 = x_10;
x_580 = x_618;
x_581 = lean_box(0);
goto block_614;
}
}
else
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; 
lean_dec_ref(x_574);
lean_dec(x_568);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_656 = lean_ctor_get(x_615, 0);
lean_inc(x_656);
x_657 = lean_ctor_get(x_615, 1);
lean_inc(x_657);
if (lean_is_exclusive(x_615)) {
 lean_ctor_release(x_615, 0);
 lean_ctor_release(x_615, 1);
 x_658 = x_615;
} else {
 lean_dec_ref(x_615);
 x_658 = lean_box(0);
}
if (lean_is_scalar(x_573)) {
 x_659 = lean_alloc_ctor(0, 3, 1);
} else {
 x_659 = x_573;
}
lean_ctor_set(x_659, 0, x_657);
lean_ctor_set(x_659, 1, x_571);
lean_ctor_set(x_659, 2, x_572);
lean_ctor_set_uint8(x_659, sizeof(void*)*3, x_570);
if (lean_is_scalar(x_658)) {
 x_660 = lean_alloc_ctor(1, 2, 0);
} else {
 x_660 = x_658;
}
lean_ctor_set(x_660, 0, x_656);
lean_ctor_set(x_660, 1, x_659);
return x_660;
}
block_614:
{
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_582; uint64_t x_583; lean_object* x_584; uint8_t x_585; 
x_582 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_582);
lean_dec_ref(x_3);
x_583 = lean_ctor_get_uint64(x_582, sizeof(void*)*3);
x_584 = lean_ctor_get(x_582, 1);
lean_inc(x_584);
lean_dec_ref(x_582);
x_585 = lean_uint64_dec_eq(x_583, x_2);
if (x_585 == 0)
{
lean_dec(x_584);
lean_dec_ref(x_579);
lean_dec(x_578);
lean_dec(x_577);
lean_dec(x_576);
lean_dec_ref(x_575);
lean_dec_ref(x_574);
lean_dec(x_568);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_13 = x_580;
x_14 = lean_box(0);
goto block_17;
}
else
{
if (lean_obj_tag(x_584) == 1)
{
lean_object* x_586; lean_object* x_587; 
x_586 = lean_ctor_get(x_584, 0);
lean_inc(x_586);
lean_dec_ref(x_584);
lean_inc(x_586);
x_587 = lean_apply_8(x_1, x_586, x_575, x_576, x_577, x_578, x_579, x_580, lean_box(0));
if (lean_obj_tag(x_587) == 0)
{
lean_object* x_588; 
x_588 = lean_ctor_get(x_587, 0);
lean_inc(x_588);
if (lean_obj_tag(x_588) == 1)
{
uint8_t x_589; 
x_589 = lean_unbox(x_568);
lean_dec(x_568);
if (x_589 == 0)
{
lean_object* x_590; lean_object* x_591; 
lean_dec(x_586);
lean_dec_ref(x_574);
lean_dec_ref(x_4);
x_590 = lean_ctor_get(x_587, 1);
lean_inc(x_590);
lean_dec_ref(x_587);
x_591 = lean_ctor_get(x_588, 0);
lean_inc(x_591);
lean_dec_ref(x_588);
x_18 = x_591;
x_19 = x_590;
x_20 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; uint8_t x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; 
x_592 = lean_ctor_get(x_587, 1);
lean_inc(x_592);
if (lean_is_exclusive(x_587)) {
 lean_ctor_release(x_587, 0);
 lean_ctor_release(x_587, 1);
 x_593 = x_587;
} else {
 lean_dec_ref(x_587);
 x_593 = lean_box(0);
}
x_594 = lean_ctor_get(x_588, 0);
lean_inc(x_594);
lean_dec_ref(x_588);
x_595 = lean_ctor_get(x_592, 0);
x_596 = lean_ctor_get_uint8(x_592, sizeof(void*)*3);
x_597 = lean_ctor_get(x_592, 1);
x_598 = lean_ctor_get(x_592, 2);
x_599 = l_Lake_Cache_writeOutputsCore(x_4, x_574, x_2, x_586);
if (lean_obj_tag(x_599) == 0)
{
lean_dec_ref(x_599);
lean_dec(x_593);
x_18 = x_594;
x_19 = x_592;
x_20 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; uint8_t x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; 
lean_inc(x_598);
lean_inc_ref(x_597);
lean_inc_ref(x_595);
lean_dec(x_594);
if (lean_is_exclusive(x_592)) {
 lean_ctor_release(x_592, 0);
 lean_ctor_release(x_592, 1);
 lean_ctor_release(x_592, 2);
 x_600 = x_592;
} else {
 lean_dec_ref(x_592);
 x_600 = lean_box(0);
}
x_601 = lean_ctor_get(x_599, 0);
lean_inc(x_601);
lean_dec_ref(x_599);
x_602 = lean_io_error_to_string(x_601);
x_603 = 3;
x_604 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_604, 0, x_602);
lean_ctor_set_uint8(x_604, sizeof(void*)*1, x_603);
x_605 = lean_array_get_size(x_595);
x_606 = lean_array_push(x_595, x_604);
if (lean_is_scalar(x_600)) {
 x_607 = lean_alloc_ctor(0, 3, 1);
} else {
 x_607 = x_600;
}
lean_ctor_set(x_607, 0, x_606);
lean_ctor_set(x_607, 1, x_597);
lean_ctor_set(x_607, 2, x_598);
lean_ctor_set_uint8(x_607, sizeof(void*)*3, x_596);
if (lean_is_scalar(x_593)) {
 x_608 = lean_alloc_ctor(1, 2, 0);
} else {
 x_608 = x_593;
 lean_ctor_set_tag(x_608, 1);
}
lean_ctor_set(x_608, 0, x_605);
lean_ctor_set(x_608, 1, x_607);
return x_608;
}
}
}
else
{
lean_object* x_609; 
lean_dec(x_588);
lean_dec(x_586);
lean_dec_ref(x_574);
lean_dec(x_568);
lean_dec_ref(x_4);
x_609 = lean_ctor_get(x_587, 1);
lean_inc(x_609);
lean_dec_ref(x_587);
x_13 = x_609;
x_14 = lean_box(0);
goto block_17;
}
}
else
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
lean_dec(x_586);
lean_dec_ref(x_574);
lean_dec(x_568);
lean_dec_ref(x_4);
x_610 = lean_ctor_get(x_587, 0);
lean_inc(x_610);
x_611 = lean_ctor_get(x_587, 1);
lean_inc(x_611);
if (lean_is_exclusive(x_587)) {
 lean_ctor_release(x_587, 0);
 lean_ctor_release(x_587, 1);
 x_612 = x_587;
} else {
 lean_dec_ref(x_587);
 x_612 = lean_box(0);
}
if (lean_is_scalar(x_612)) {
 x_613 = lean_alloc_ctor(1, 2, 0);
} else {
 x_613 = x_612;
}
lean_ctor_set(x_613, 0, x_610);
lean_ctor_set(x_613, 1, x_611);
return x_613;
}
}
else
{
lean_dec(x_584);
lean_dec_ref(x_579);
lean_dec(x_578);
lean_dec(x_577);
lean_dec(x_576);
lean_dec_ref(x_575);
lean_dec_ref(x_574);
lean_dec(x_568);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_13 = x_580;
x_14 = lean_box(0);
goto block_17;
}
}
}
else
{
lean_dec_ref(x_579);
lean_dec(x_578);
lean_dec(x_577);
lean_dec(x_576);
lean_dec_ref(x_575);
lean_dec_ref(x_574);
lean_dec(x_568);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_13 = x_580;
x_14 = lean_box(0);
goto block_17;
}
}
}
else
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_661 = lean_ctor_get(x_566, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_566, 1);
lean_inc(x_662);
if (lean_is_exclusive(x_566)) {
 lean_ctor_release(x_566, 0);
 lean_ctor_release(x_566, 1);
 x_663 = x_566;
} else {
 lean_dec_ref(x_566);
 x_663 = lean_box(0);
}
if (lean_is_scalar(x_663)) {
 x_664 = lean_alloc_ctor(1, 2, 0);
} else {
 x_664 = x_663;
}
lean_ctor_set(x_664, 0, x_661);
lean_ctor_set(x_664, 1, x_662);
return x_664;
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
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lake_getArtifacts_x3f___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
x_32 = l_Lake_cacheArtifact___redArg___closed__0;
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
x_33 = l_Lake_cacheArtifact___redArg___closed__0;
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
x_11 = lean_box(0);
x_12 = x_9;
x_13 = x_21;
goto block_18;
}
else
{
lean_object* x_22; 
lean_dec_ref(x_19);
x_22 = l_Lake_platformTrace___closed__4;
x_11 = lean_box(0);
x_12 = x_9;
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
lean_ctor_set(x_17, 1, x_12);
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
LEAN_EXPORT lean_object* l_Lake_computeArtifact(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_computeArtifact___redArg(x_1, x_2, x_3, x_8, x_9);
return x_11;
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
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get_uint8(x_21, sizeof(void*)*2 + 2);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
x_26 = lean_io_mono_ms_now();
x_27 = l_Lake_JobAction_merge(x_25, x_9);
lean_inc_ref(x_24);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_27);
lean_inc_ref(x_13);
x_28 = lean_apply_7(x_1, x_6, x_10, x_11, x_12, x_13, x_14, lean_box(0));
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_28, 1);
lean_inc(x_36);
lean_dec_ref(x_28);
x_37 = lean_ctor_get(x_36, 0);
x_38 = lean_ctor_get_uint8(x_36, sizeof(void*)*3);
x_39 = lean_ctor_get(x_36, 1);
x_40 = lean_ctor_get(x_36, 2);
lean_inc_ref(x_2);
x_41 = l_Lake_clearFileHash(x_2);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
lean_dec_ref(x_41);
x_42 = l_Lake_removeFileIfExists(x_3);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_43 = x_42;
} else {
 lean_dec_ref(x_42);
 x_43 = lean_box(0);
}
x_44 = l_Lake_computeArtifact___redArg(x_2, x_4, x_5, x_13, x_36);
lean_dec_ref(x_13);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; uint64_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_47 = x_44;
} else {
 lean_dec_ref(x_44);
 x_47 = lean_box(0);
}
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ctor_get(x_45, 0);
x_50 = lean_ctor_get_uint8(x_45, sizeof(void*)*3);
x_51 = lean_ctor_get(x_45, 1);
x_52 = lean_ctor_get(x_45, 2);
x_53 = lean_ctor_get_uint64(x_48, sizeof(void*)*1);
x_54 = lean_ctor_get(x_48, 0);
x_55 = lean_array_get_size(x_24);
lean_dec_ref(x_24);
x_56 = lean_array_get_size(x_49);
x_57 = l_Array_extract___redArg(x_49, x_55, x_56);
x_94 = lean_string_utf8_byte_size(x_54);
x_95 = lean_unsigned_to_nat(0u);
x_96 = lean_nat_dec_eq(x_94, x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = l_Lake_Hash_hex(x_53);
x_98 = l_Lake_instToOutputJsonArtifact___lam__0___closed__0;
x_99 = lean_string_append(x_97, x_98);
x_100 = lean_string_append(x_99, x_54);
x_58 = x_100;
goto block_93;
}
else
{
lean_object* x_101; 
x_101 = l_Lake_Hash_hex(x_53);
x_58 = x_101;
goto block_93;
}
block_93:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
if (lean_is_scalar(x_43)) {
 x_59 = lean_alloc_ctor(3, 1, 0);
} else {
 x_59 = x_43;
 lean_ctor_set_tag(x_59, 3);
}
lean_ctor_set(x_59, 0, x_58);
x_60 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_7, x_59, x_57);
x_61 = l_Lake_BuildMetadata_writeFile(x_8, x_60);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_63 = lean_ctor_get(x_61, 0);
lean_dec(x_63);
x_64 = lean_box(0);
lean_inc(x_46);
if (lean_is_scalar(x_47)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_47;
 lean_ctor_set_tag(x_65, 1);
}
lean_ctor_set(x_65, 0, x_46);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 0, x_65);
x_66 = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(x_26, x_61, x_45);
lean_dec_ref(x_61);
lean_dec(x_26);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_66, 0);
lean_dec(x_68);
lean_ctor_set(x_66, 0, x_46);
return x_66;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_46);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_61);
x_71 = lean_box(0);
lean_inc(x_46);
if (lean_is_scalar(x_47)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_47;
 lean_ctor_set_tag(x_72, 1);
}
lean_ctor_set(x_72, 0, x_46);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(x_26, x_73, x_45);
lean_dec_ref(x_73);
lean_dec(x_26);
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
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_46);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
uint8_t x_78; 
lean_inc(x_52);
lean_inc_ref(x_51);
lean_inc_ref(x_49);
lean_dec(x_47);
lean_dec(x_46);
x_78 = !lean_is_exclusive(x_45);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; 
x_79 = lean_ctor_get(x_45, 2);
lean_dec(x_79);
x_80 = lean_ctor_get(x_45, 1);
lean_dec(x_80);
x_81 = lean_ctor_get(x_45, 0);
lean_dec(x_81);
x_82 = lean_ctor_get(x_61, 0);
lean_inc(x_82);
lean_dec_ref(x_61);
x_83 = lean_io_error_to_string(x_82);
x_84 = 3;
x_85 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set_uint8(x_85, sizeof(void*)*1, x_84);
x_86 = lean_array_push(x_49, x_85);
lean_ctor_set(x_45, 0, x_86);
x_29 = x_56;
x_30 = x_45;
x_31 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_45);
x_87 = lean_ctor_get(x_61, 0);
lean_inc(x_87);
lean_dec_ref(x_61);
x_88 = lean_io_error_to_string(x_87);
x_89 = 3;
x_90 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set_uint8(x_90, sizeof(void*)*1, x_89);
x_91 = lean_array_push(x_49, x_90);
x_92 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_51);
lean_ctor_set(x_92, 2, x_52);
lean_ctor_set_uint8(x_92, sizeof(void*)*3, x_50);
x_29 = x_56;
x_30 = x_92;
x_31 = lean_box(0);
goto block_35;
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_43);
lean_dec_ref(x_24);
lean_dec_ref(x_8);
x_102 = lean_ctor_get(x_44, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_44, 1);
lean_inc(x_103);
lean_dec_ref(x_44);
x_29 = x_102;
x_30 = x_103;
x_31 = lean_box(0);
goto block_35;
}
}
else
{
uint8_t x_104; 
lean_inc(x_40);
lean_inc_ref(x_39);
lean_inc_ref(x_37);
lean_dec_ref(x_24);
lean_dec_ref(x_13);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_104 = !lean_is_exclusive(x_36);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_105 = lean_ctor_get(x_36, 2);
lean_dec(x_105);
x_106 = lean_ctor_get(x_36, 1);
lean_dec(x_106);
x_107 = lean_ctor_get(x_36, 0);
lean_dec(x_107);
x_108 = lean_ctor_get(x_42, 0);
lean_inc(x_108);
lean_dec_ref(x_42);
x_109 = lean_io_error_to_string(x_108);
x_110 = 3;
x_111 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set_uint8(x_111, sizeof(void*)*1, x_110);
x_112 = lean_array_get_size(x_37);
x_113 = lean_array_push(x_37, x_111);
lean_ctor_set(x_36, 0, x_113);
x_29 = x_112;
x_30 = x_36;
x_31 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_36);
x_114 = lean_ctor_get(x_42, 0);
lean_inc(x_114);
lean_dec_ref(x_42);
x_115 = lean_io_error_to_string(x_114);
x_116 = 3;
x_117 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set_uint8(x_117, sizeof(void*)*1, x_116);
x_118 = lean_array_get_size(x_37);
x_119 = lean_array_push(x_37, x_117);
x_120 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_39);
lean_ctor_set(x_120, 2, x_40);
lean_ctor_set_uint8(x_120, sizeof(void*)*3, x_38);
x_29 = x_118;
x_30 = x_120;
x_31 = lean_box(0);
goto block_35;
}
}
}
else
{
uint8_t x_121; 
lean_inc(x_40);
lean_inc_ref(x_39);
lean_inc_ref(x_37);
lean_dec_ref(x_24);
lean_dec_ref(x_13);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_121 = !lean_is_exclusive(x_36);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_122 = lean_ctor_get(x_36, 2);
lean_dec(x_122);
x_123 = lean_ctor_get(x_36, 1);
lean_dec(x_123);
x_124 = lean_ctor_get(x_36, 0);
lean_dec(x_124);
x_125 = lean_ctor_get(x_41, 0);
lean_inc(x_125);
lean_dec_ref(x_41);
x_126 = lean_io_error_to_string(x_125);
x_127 = 3;
x_128 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set_uint8(x_128, sizeof(void*)*1, x_127);
x_129 = lean_array_get_size(x_37);
x_130 = lean_array_push(x_37, x_128);
lean_ctor_set(x_36, 0, x_130);
x_29 = x_129;
x_30 = x_36;
x_31 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_36);
x_131 = lean_ctor_get(x_41, 0);
lean_inc(x_131);
lean_dec_ref(x_41);
x_132 = lean_io_error_to_string(x_131);
x_133 = 3;
x_134 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set_uint8(x_134, sizeof(void*)*1, x_133);
x_135 = lean_array_get_size(x_37);
x_136 = lean_array_push(x_37, x_134);
x_137 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_39);
lean_ctor_set(x_137, 2, x_40);
lean_ctor_set_uint8(x_137, sizeof(void*)*3, x_38);
x_29 = x_135;
x_30 = x_137;
x_31 = lean_box(0);
goto block_35;
}
}
}
else
{
lean_object* x_138; lean_object* x_139; 
lean_dec_ref(x_24);
lean_dec_ref(x_13);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_138 = lean_ctor_get(x_28, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_28, 1);
lean_inc(x_139);
lean_dec_ref(x_28);
x_29 = x_138;
x_30 = x_139;
x_31 = lean_box(0);
goto block_35;
}
block_35:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_box(0);
x_33 = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(x_26, x_32, x_30);
lean_dec(x_26);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec_ref(x_33);
x_16 = x_29;
x_17 = x_34;
x_18 = lean_box(0);
goto block_20;
}
}
else
{
lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_140 = lean_ctor_get(x_14, 0);
x_141 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
x_142 = lean_ctor_get(x_14, 1);
x_143 = lean_ctor_get(x_14, 2);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_140);
lean_dec(x_14);
x_144 = lean_io_mono_ms_now();
x_145 = l_Lake_JobAction_merge(x_141, x_9);
lean_inc_ref(x_140);
x_146 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_146, 0, x_140);
lean_ctor_set(x_146, 1, x_142);
lean_ctor_set(x_146, 2, x_143);
lean_ctor_set_uint8(x_146, sizeof(void*)*3, x_145);
lean_inc_ref(x_13);
x_147 = lean_apply_7(x_1, x_6, x_10, x_11, x_12, x_13, x_146, lean_box(0));
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_155 = lean_ctor_get(x_147, 1);
lean_inc(x_155);
lean_dec_ref(x_147);
x_156 = lean_ctor_get(x_155, 0);
x_157 = lean_ctor_get_uint8(x_155, sizeof(void*)*3);
x_158 = lean_ctor_get(x_155, 1);
x_159 = lean_ctor_get(x_155, 2);
lean_inc_ref(x_2);
x_160 = l_Lake_clearFileHash(x_2);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; 
lean_dec_ref(x_160);
x_161 = l_Lake_removeFileIfExists(x_3);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; 
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 x_162 = x_161;
} else {
 lean_dec_ref(x_161);
 x_162 = lean_box(0);
}
x_163 = l_Lake_computeArtifact___redArg(x_2, x_4, x_5, x_13, x_155);
lean_dec_ref(x_13);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; lean_object* x_171; uint64_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 0);
lean_inc(x_165);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_166 = x_163;
} else {
 lean_dec_ref(x_163);
 x_166 = lean_box(0);
}
x_167 = lean_ctor_get(x_165, 0);
x_168 = lean_ctor_get(x_164, 0);
x_169 = lean_ctor_get_uint8(x_164, sizeof(void*)*3);
x_170 = lean_ctor_get(x_164, 1);
x_171 = lean_ctor_get(x_164, 2);
x_172 = lean_ctor_get_uint64(x_167, sizeof(void*)*1);
x_173 = lean_ctor_get(x_167, 0);
x_174 = lean_array_get_size(x_140);
lean_dec_ref(x_140);
x_175 = lean_array_get_size(x_168);
x_176 = l_Array_extract___redArg(x_168, x_174, x_175);
x_197 = lean_string_utf8_byte_size(x_173);
x_198 = lean_unsigned_to_nat(0u);
x_199 = lean_nat_dec_eq(x_197, x_198);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_200 = l_Lake_Hash_hex(x_172);
x_201 = l_Lake_instToOutputJsonArtifact___lam__0___closed__0;
x_202 = lean_string_append(x_200, x_201);
x_203 = lean_string_append(x_202, x_173);
x_177 = x_203;
goto block_196;
}
else
{
lean_object* x_204; 
x_204 = l_Lake_Hash_hex(x_172);
x_177 = x_204;
goto block_196;
}
block_196:
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
if (lean_is_scalar(x_162)) {
 x_178 = lean_alloc_ctor(3, 1, 0);
} else {
 x_178 = x_162;
 lean_ctor_set_tag(x_178, 3);
}
lean_ctor_set(x_178, 0, x_177);
x_179 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_7, x_178, x_176);
x_180 = l_Lake_BuildMetadata_writeFile(x_8, x_179);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 x_181 = x_180;
} else {
 lean_dec_ref(x_180);
 x_181 = lean_box(0);
}
x_182 = lean_box(0);
lean_inc(x_165);
if (lean_is_scalar(x_166)) {
 x_183 = lean_alloc_ctor(1, 2, 0);
} else {
 x_183 = x_166;
 lean_ctor_set_tag(x_183, 1);
}
lean_ctor_set(x_183, 0, x_165);
lean_ctor_set(x_183, 1, x_182);
if (lean_is_scalar(x_181)) {
 x_184 = lean_alloc_ctor(1, 1, 0);
} else {
 x_184 = x_181;
 lean_ctor_set_tag(x_184, 1);
}
lean_ctor_set(x_184, 0, x_183);
x_185 = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(x_144, x_184, x_164);
lean_dec_ref(x_184);
lean_dec(x_144);
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_187 = x_185;
} else {
 lean_dec_ref(x_185);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_165);
lean_ctor_set(x_188, 1, x_186);
return x_188;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_inc(x_171);
lean_inc_ref(x_170);
lean_inc_ref(x_168);
lean_dec(x_166);
lean_dec(x_165);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 lean_ctor_release(x_164, 2);
 x_189 = x_164;
} else {
 lean_dec_ref(x_164);
 x_189 = lean_box(0);
}
x_190 = lean_ctor_get(x_180, 0);
lean_inc(x_190);
lean_dec_ref(x_180);
x_191 = lean_io_error_to_string(x_190);
x_192 = 3;
x_193 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set_uint8(x_193, sizeof(void*)*1, x_192);
x_194 = lean_array_push(x_168, x_193);
if (lean_is_scalar(x_189)) {
 x_195 = lean_alloc_ctor(0, 3, 1);
} else {
 x_195 = x_189;
}
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_170);
lean_ctor_set(x_195, 2, x_171);
lean_ctor_set_uint8(x_195, sizeof(void*)*3, x_169);
x_148 = x_175;
x_149 = x_195;
x_150 = lean_box(0);
goto block_154;
}
}
}
else
{
lean_object* x_205; lean_object* x_206; 
lean_dec(x_162);
lean_dec_ref(x_140);
lean_dec_ref(x_8);
x_205 = lean_ctor_get(x_163, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_163, 1);
lean_inc(x_206);
lean_dec_ref(x_163);
x_148 = x_205;
x_149 = x_206;
x_150 = lean_box(0);
goto block_154;
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_inc(x_159);
lean_inc_ref(x_158);
lean_inc_ref(x_156);
lean_dec_ref(x_140);
lean_dec_ref(x_13);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 lean_ctor_release(x_155, 2);
 x_207 = x_155;
} else {
 lean_dec_ref(x_155);
 x_207 = lean_box(0);
}
x_208 = lean_ctor_get(x_161, 0);
lean_inc(x_208);
lean_dec_ref(x_161);
x_209 = lean_io_error_to_string(x_208);
x_210 = 3;
x_211 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set_uint8(x_211, sizeof(void*)*1, x_210);
x_212 = lean_array_get_size(x_156);
x_213 = lean_array_push(x_156, x_211);
if (lean_is_scalar(x_207)) {
 x_214 = lean_alloc_ctor(0, 3, 1);
} else {
 x_214 = x_207;
}
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_158);
lean_ctor_set(x_214, 2, x_159);
lean_ctor_set_uint8(x_214, sizeof(void*)*3, x_157);
x_148 = x_212;
x_149 = x_214;
x_150 = lean_box(0);
goto block_154;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_inc(x_159);
lean_inc_ref(x_158);
lean_inc_ref(x_156);
lean_dec_ref(x_140);
lean_dec_ref(x_13);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 lean_ctor_release(x_155, 2);
 x_215 = x_155;
} else {
 lean_dec_ref(x_155);
 x_215 = lean_box(0);
}
x_216 = lean_ctor_get(x_160, 0);
lean_inc(x_216);
lean_dec_ref(x_160);
x_217 = lean_io_error_to_string(x_216);
x_218 = 3;
x_219 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set_uint8(x_219, sizeof(void*)*1, x_218);
x_220 = lean_array_get_size(x_156);
x_221 = lean_array_push(x_156, x_219);
if (lean_is_scalar(x_215)) {
 x_222 = lean_alloc_ctor(0, 3, 1);
} else {
 x_222 = x_215;
}
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_158);
lean_ctor_set(x_222, 2, x_159);
lean_ctor_set_uint8(x_222, sizeof(void*)*3, x_157);
x_148 = x_220;
x_149 = x_222;
x_150 = lean_box(0);
goto block_154;
}
}
else
{
lean_object* x_223; lean_object* x_224; 
lean_dec_ref(x_140);
lean_dec_ref(x_13);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_223 = lean_ctor_get(x_147, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_147, 1);
lean_inc(x_224);
lean_dec_ref(x_147);
x_148 = x_223;
x_149 = x_224;
x_150 = lean_box(0);
goto block_154;
}
block_154:
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_box(0);
x_152 = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(x_144, x_151, x_149);
lean_dec(x_144);
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
lean_dec_ref(x_152);
x_16 = x_148;
x_17 = x_153;
x_18 = lean_box(0);
goto block_20;
}
}
}
else
{
uint8_t x_225; 
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_225 = !lean_is_exclusive(x_14);
if (x_225 == 0)
{
lean_object* x_226; uint8_t x_227; uint8_t x_228; uint8_t x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_226 = lean_ctor_get(x_14, 0);
x_227 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
x_228 = 3;
x_229 = l_Lake_JobAction_merge(x_227, x_228);
x_230 = l_Lake_buildAction___redArg___closed__1;
x_231 = lean_array_get_size(x_226);
x_232 = lean_array_push(x_226, x_230);
lean_ctor_set(x_14, 0, x_232);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_229);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_14);
return x_233;
}
else
{
lean_object* x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; uint8_t x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_234 = lean_ctor_get(x_14, 0);
x_235 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
x_236 = lean_ctor_get(x_14, 1);
x_237 = lean_ctor_get(x_14, 2);
lean_inc(x_237);
lean_inc(x_236);
lean_inc(x_234);
lean_dec(x_14);
x_238 = 3;
x_239 = l_Lake_JobAction_merge(x_235, x_238);
x_240 = l_Lake_buildAction___redArg___closed__1;
x_241 = lean_array_get_size(x_234);
x_242 = lean_array_push(x_234, x_240);
x_243 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_236);
lean_ctor_set(x_243, 2, x_237);
lean_ctor_set_uint8(x_243, sizeof(void*)*3, x_239);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_241);
lean_ctor_set(x_244, 1, x_243);
return x_244;
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
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_5);
x_17 = lean_unbox(x_9);
x_18 = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(x_1, x_2, x_3, x_4, x_16, x_6, x_7, x_8, x_17, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = 3;
lean_inc_ref(x_6);
x_15 = l_Lake_buildAction___at___00__private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(x_2, x_1, x_6, x_4, x_3, x_7, x_5, x_6, x_14, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_6);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
x_15 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheEnabled___at___00Lake_buildArtifactUnlessUpToDate_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 6);
x_6 = lean_ctor_get(x_5, 25);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 1);
x_8 = l_Lake_Workspace_enableArtifactCache(x_7);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheEnabled___at___00Lake_buildArtifactUnlessUpToDate_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Package_isArtifactCacheEnabled___at___00Lake_buildArtifactUnlessUpToDate_spec__0___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheEnabled___at___00Lake_buildArtifactUnlessUpToDate_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Package_isArtifactCacheEnabled___at___00Lake_buildArtifactUnlessUpToDate_spec__0___redArg(x_1, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheEnabled___at___00Lake_buildArtifactUnlessUpToDate_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Package_isArtifactCacheEnabled___at___00Lake_buildArtifactUnlessUpToDate_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_98; 
x_23 = l_Lake_Package_isArtifactCacheEnabled___at___00Lake_buildArtifactUnlessUpToDate_spec__0___redArg(x_5, x_9, x_10);
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
lean_inc_ref(x_32);
lean_inc_ref(x_4);
x_98 = l_Lake_Cache_readOutputs_x3f(x_4, x_32, x_2, x_27);
if (lean_obj_tag(x_98) == 0)
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_98, 0);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_30);
lean_inc_ref(x_29);
lean_inc(x_101);
x_102 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_29);
lean_ctor_set(x_102, 2, x_30);
lean_ctor_set_uint8(x_102, sizeof(void*)*3, x_28);
if (lean_obj_tag(x_100) == 1)
{
uint8_t x_103; 
x_103 = !lean_is_exclusive(x_100);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_100, 0);
lean_inc(x_104);
x_105 = l_Lake_ArtifactDescr_fromJson_x3f(x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_free_object(x_100);
lean_dec_ref(x_102);
lean_free_object(x_98);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
lean_dec_ref(x_105);
x_107 = l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__0;
x_108 = lean_unsigned_to_nat(80u);
x_109 = l_Lean_Json_pretty(x_104, x_108);
x_110 = lean_string_append(x_107, x_109);
lean_dec_ref(x_109);
x_111 = l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__1;
x_112 = lean_string_append(x_110, x_111);
x_113 = lean_string_append(x_112, x_106);
lean_dec(x_106);
x_74 = x_113;
x_75 = x_101;
x_76 = x_28;
x_77 = x_29;
x_78 = x_30;
x_79 = lean_box(0);
goto block_97;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_104);
x_114 = lean_ctor_get(x_9, 1);
x_115 = lean_ctor_get(x_105, 0);
lean_inc(x_115);
lean_dec_ref(x_105);
x_116 = lean_ctor_get(x_114, 2);
lean_inc_ref(x_116);
x_117 = l_Lake_Cache_getArtifact(x_116, x_115);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; 
lean_dec(x_101);
lean_dec_ref(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_9);
lean_dec_ref(x_4);
lean_dec(x_3);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
lean_dec_ref(x_117);
lean_ctor_set(x_100, 0, x_118);
lean_ctor_set(x_98, 1, x_102);
return x_98;
}
else
{
lean_object* x_119; 
lean_free_object(x_100);
lean_dec_ref(x_102);
lean_free_object(x_98);
x_119 = lean_ctor_get(x_117, 0);
lean_inc(x_119);
lean_dec_ref(x_117);
x_74 = x_119;
x_75 = x_101;
x_76 = x_28;
x_77 = x_29;
x_78 = x_30;
x_79 = lean_box(0);
goto block_97;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_100, 0);
lean_inc(x_120);
lean_dec(x_100);
lean_inc(x_120);
x_121 = l_Lake_ArtifactDescr_fromJson_x3f(x_120);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec_ref(x_102);
lean_free_object(x_98);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
lean_dec_ref(x_121);
x_123 = l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__0;
x_124 = lean_unsigned_to_nat(80u);
x_125 = l_Lean_Json_pretty(x_120, x_124);
x_126 = lean_string_append(x_123, x_125);
lean_dec_ref(x_125);
x_127 = l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__1;
x_128 = lean_string_append(x_126, x_127);
x_129 = lean_string_append(x_128, x_122);
lean_dec(x_122);
x_74 = x_129;
x_75 = x_101;
x_76 = x_28;
x_77 = x_29;
x_78 = x_30;
x_79 = lean_box(0);
goto block_97;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_120);
x_130 = lean_ctor_get(x_9, 1);
x_131 = lean_ctor_get(x_121, 0);
lean_inc(x_131);
lean_dec_ref(x_121);
x_132 = lean_ctor_get(x_130, 2);
lean_inc_ref(x_132);
x_133 = l_Lake_Cache_getArtifact(x_132, x_131);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_101);
lean_dec_ref(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_9);
lean_dec_ref(x_4);
lean_dec(x_3);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
lean_dec_ref(x_133);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_98, 1, x_102);
lean_ctor_set(x_98, 0, x_135);
return x_98;
}
else
{
lean_object* x_136; 
lean_dec_ref(x_102);
lean_free_object(x_98);
x_136 = lean_ctor_get(x_133, 0);
lean_inc(x_136);
lean_dec_ref(x_133);
x_74 = x_136;
x_75 = x_101;
x_76 = x_28;
x_77 = x_29;
x_78 = x_30;
x_79 = lean_box(0);
goto block_97;
}
}
}
}
else
{
lean_free_object(x_98);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
x_33 = x_9;
x_34 = x_102;
x_35 = lean_box(0);
goto block_73;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_98, 0);
x_138 = lean_ctor_get(x_98, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_98);
lean_inc(x_30);
lean_inc_ref(x_29);
lean_inc(x_138);
x_139 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_29);
lean_ctor_set(x_139, 2, x_30);
lean_ctor_set_uint8(x_139, sizeof(void*)*3, x_28);
if (lean_obj_tag(x_137) == 1)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_137, 0);
lean_inc(x_140);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 x_141 = x_137;
} else {
 lean_dec_ref(x_137);
 x_141 = lean_box(0);
}
lean_inc(x_140);
x_142 = l_Lake_ArtifactDescr_fromJson_x3f(x_140);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_141);
lean_dec_ref(x_139);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
lean_dec_ref(x_142);
x_144 = l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__0;
x_145 = lean_unsigned_to_nat(80u);
x_146 = l_Lean_Json_pretty(x_140, x_145);
x_147 = lean_string_append(x_144, x_146);
lean_dec_ref(x_146);
x_148 = l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__1;
x_149 = lean_string_append(x_147, x_148);
x_150 = lean_string_append(x_149, x_143);
lean_dec(x_143);
x_74 = x_150;
x_75 = x_138;
x_76 = x_28;
x_77 = x_29;
x_78 = x_30;
x_79 = lean_box(0);
goto block_97;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_140);
x_151 = lean_ctor_get(x_9, 1);
x_152 = lean_ctor_get(x_142, 0);
lean_inc(x_152);
lean_dec_ref(x_142);
x_153 = lean_ctor_get(x_151, 2);
lean_inc_ref(x_153);
x_154 = l_Lake_Cache_getArtifact(x_153, x_152);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_138);
lean_dec_ref(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_9);
lean_dec_ref(x_4);
lean_dec(x_3);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
lean_dec_ref(x_154);
if (lean_is_scalar(x_141)) {
 x_156 = lean_alloc_ctor(1, 1, 0);
} else {
 x_156 = x_141;
}
lean_ctor_set(x_156, 0, x_155);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_139);
return x_157;
}
else
{
lean_object* x_158; 
lean_dec(x_141);
lean_dec_ref(x_139);
x_158 = lean_ctor_get(x_154, 0);
lean_inc(x_158);
lean_dec_ref(x_154);
x_74 = x_158;
x_75 = x_138;
x_76 = x_28;
x_77 = x_29;
x_78 = x_30;
x_79 = lean_box(0);
goto block_97;
}
}
}
else
{
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
x_33 = x_9;
x_34 = x_139;
x_35 = lean_box(0);
goto block_73;
}
}
}
else
{
uint8_t x_159; 
lean_dec_ref(x_32);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_9);
lean_dec_ref(x_4);
lean_dec(x_3);
x_159 = !lean_is_exclusive(x_98);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_98, 1);
x_161 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_29);
lean_ctor_set(x_161, 2, x_30);
lean_ctor_set_uint8(x_161, sizeof(void*)*3, x_28);
lean_ctor_set(x_98, 1, x_161);
return x_98;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_162 = lean_ctor_get(x_98, 0);
x_163 = lean_ctor_get(x_98, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_98);
x_164 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_29);
lean_ctor_set(x_164, 2, x_30);
lean_ctor_set_uint8(x_164, sizeof(void*)*3, x_28);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_164);
return x_165;
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
if (lean_obj_tag(x_38) == 1)
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
else
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
block_97:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_80 = l_Lake_Hash_hex(x_2);
x_81 = lean_string_utf8_byte_size(x_80);
x_82 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_80);
x_83 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_82);
lean_ctor_set(x_83, 2, x_81);
x_84 = lean_unsigned_to_nat(7u);
x_85 = l_String_Slice_Pos_nextn(x_83, x_82, x_84);
lean_dec_ref(x_83);
x_86 = l_Lake_getArtifacts_x3f___redArg___closed__0;
x_87 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_87, 0, x_80);
lean_ctor_set(x_87, 1, x_82);
lean_ctor_set(x_87, 2, x_85);
x_88 = l_String_Slice_toString(x_87);
lean_dec_ref(x_87);
x_89 = lean_string_append(x_86, x_88);
lean_dec_ref(x_88);
x_90 = l_Lake_getArtifacts_x3f___redArg___closed__1;
x_91 = lean_string_append(x_89, x_90);
x_92 = lean_string_append(x_91, x_74);
lean_dec_ref(x_74);
x_93 = 2;
x_94 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set_uint8(x_94, sizeof(void*)*1, x_93);
x_95 = lean_array_push(x_75, x_94);
if (lean_is_scalar(x_31)) {
 x_96 = lean_alloc_ctor(0, 3, 1);
} else {
 x_96 = x_31;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_77);
lean_ctor_set(x_96, 2, x_78);
lean_ctor_set_uint8(x_96, sizeof(void*)*3, x_76);
x_33 = x_9;
x_34 = x_96;
x_35 = lean_box(0);
goto block_73;
}
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint64_t x_12; lean_object* x_13; 
x_12 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_13 = l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_13;
}
}
static lean_object* _init_l_Lake_buildArtifactUnlessUpToDate___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("restored artifact from cache to: ", 33, 33);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0(uint64_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
lean_inc(x_2);
x_16 = l_Lake_getArtifacts_x3f___at___00Lake_buildArtifactUnlessUpToDate_spec__1(x_9, x_1, x_2, x_3, x_4, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_34; lean_object* x_35; lean_object* x_63; lean_object* x_64; lean_object* x_143; 
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
lean_inc(x_20);
x_143 = l_Lake_SavedTrace_replayOrFetchIfUpToDate___redArg(x_1, x_2, x_18);
lean_dec(x_2);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; uint8_t x_145; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_unbox(x_144);
lean_dec(x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_146 = lean_ctor_get(x_143, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_147 = x_143;
} else {
 lean_dec_ref(x_143);
 x_147 = lean_box(0);
}
x_148 = lean_ctor_get(x_146, 0);
x_149 = lean_ctor_get_uint8(x_146, sizeof(void*)*3);
x_150 = lean_ctor_get(x_146, 1);
x_151 = lean_ctor_get(x_146, 2);
x_152 = l_Lake_removeFileIfExists(x_5);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_178; uint64_t x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 x_153 = x_152;
} else {
 lean_dec_ref(x_152);
 x_153 = lean_box(0);
}
x_178 = lean_ctor_get(x_20, 0);
x_179 = lean_ctor_get_uint64(x_178, sizeof(void*)*1);
x_180 = lean_ctor_get(x_178, 0);
x_181 = lean_string_utf8_byte_size(x_180);
x_182 = lean_unsigned_to_nat(0u);
x_183 = lean_nat_dec_eq(x_181, x_182);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = l_Lake_Hash_hex(x_179);
x_185 = l_Lake_instToOutputJsonArtifact___lam__0___closed__0;
x_186 = lean_string_append(x_184, x_185);
x_187 = lean_string_append(x_186, x_180);
x_154 = x_187;
goto block_177;
}
else
{
lean_object* x_188; 
x_188 = l_Lake_Hash_hex(x_179);
x_154 = x_188;
goto block_177;
}
block_177:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
if (lean_is_scalar(x_153)) {
 x_155 = lean_alloc_ctor(3, 1, 0);
} else {
 x_155 = x_153;
 lean_ctor_set_tag(x_155, 3);
}
lean_ctor_set(x_155, 0, x_154);
x_156 = l_Lake_BuildMetadata_ofFetch(x_1, x_155);
x_157 = l_Lake_BuildMetadata_writeFile(x_7, x_156);
if (lean_obj_tag(x_157) == 0)
{
lean_dec_ref(x_157);
lean_dec(x_147);
x_63 = x_146;
x_64 = lean_box(0);
goto block_142;
}
else
{
uint8_t x_158; 
lean_inc(x_151);
lean_inc_ref(x_150);
lean_inc_ref(x_148);
lean_dec(x_20);
lean_dec(x_19);
lean_dec_ref(x_17);
lean_dec_ref(x_5);
x_158 = !lean_is_exclusive(x_146);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_159 = lean_ctor_get(x_146, 2);
lean_dec(x_159);
x_160 = lean_ctor_get(x_146, 1);
lean_dec(x_160);
x_161 = lean_ctor_get(x_146, 0);
lean_dec(x_161);
x_162 = lean_ctor_get(x_157, 0);
lean_inc(x_162);
lean_dec_ref(x_157);
x_163 = lean_io_error_to_string(x_162);
x_164 = 3;
x_165 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set_uint8(x_165, sizeof(void*)*1, x_164);
x_166 = lean_array_get_size(x_148);
x_167 = lean_array_push(x_148, x_165);
lean_ctor_set(x_146, 0, x_167);
if (lean_is_scalar(x_147)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_147;
 lean_ctor_set_tag(x_168, 1);
}
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_146);
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_146);
x_169 = lean_ctor_get(x_157, 0);
lean_inc(x_169);
lean_dec_ref(x_157);
x_170 = lean_io_error_to_string(x_169);
x_171 = 3;
x_172 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set_uint8(x_172, sizeof(void*)*1, x_171);
x_173 = lean_array_get_size(x_148);
x_174 = lean_array_push(x_148, x_172);
x_175 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_150);
lean_ctor_set(x_175, 2, x_151);
lean_ctor_set_uint8(x_175, sizeof(void*)*3, x_149);
if (lean_is_scalar(x_147)) {
 x_176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_176 = x_147;
 lean_ctor_set_tag(x_176, 1);
}
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
}
}
else
{
uint8_t x_189; 
lean_inc(x_151);
lean_inc_ref(x_150);
lean_inc_ref(x_148);
lean_dec(x_20);
lean_dec(x_19);
lean_dec_ref(x_17);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
x_189 = !lean_is_exclusive(x_146);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_190 = lean_ctor_get(x_146, 2);
lean_dec(x_190);
x_191 = lean_ctor_get(x_146, 1);
lean_dec(x_191);
x_192 = lean_ctor_get(x_146, 0);
lean_dec(x_192);
x_193 = lean_ctor_get(x_152, 0);
lean_inc(x_193);
lean_dec_ref(x_152);
x_194 = lean_io_error_to_string(x_193);
x_195 = 3;
x_196 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set_uint8(x_196, sizeof(void*)*1, x_195);
x_197 = lean_array_get_size(x_148);
x_198 = lean_array_push(x_148, x_196);
lean_ctor_set(x_146, 0, x_198);
if (lean_is_scalar(x_147)) {
 x_199 = lean_alloc_ctor(1, 2, 0);
} else {
 x_199 = x_147;
 lean_ctor_set_tag(x_199, 1);
}
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_146);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; uint8_t x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_146);
x_200 = lean_ctor_get(x_152, 0);
lean_inc(x_200);
lean_dec_ref(x_152);
x_201 = lean_io_error_to_string(x_200);
x_202 = 3;
x_203 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set_uint8(x_203, sizeof(void*)*1, x_202);
x_204 = lean_array_get_size(x_148);
x_205 = lean_array_push(x_148, x_203);
x_206 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_150);
lean_ctor_set(x_206, 2, x_151);
lean_ctor_set_uint8(x_206, sizeof(void*)*3, x_149);
if (lean_is_scalar(x_147)) {
 x_207 = lean_alloc_ctor(1, 2, 0);
} else {
 x_207 = x_147;
 lean_ctor_set_tag(x_207, 1);
}
lean_ctor_set(x_207, 0, x_204);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
}
else
{
lean_object* x_208; 
lean_dec_ref(x_7);
x_208 = lean_ctor_get(x_143, 1);
lean_inc(x_208);
lean_dec_ref(x_143);
x_63 = x_208;
x_64 = lean_box(0);
goto block_142;
}
}
else
{
uint8_t x_209; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec_ref(x_17);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
x_209 = !lean_is_exclusive(x_143);
if (x_209 == 0)
{
return x_143;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_143, 0);
x_211 = lean_ctor_get(x_143, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_143);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
}
block_33:
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_20, 2);
lean_dec(x_24);
x_25 = lean_ctor_get(x_20, 1);
lean_dec(x_25);
lean_inc_ref(x_5);
lean_ctor_set(x_20, 2, x_5);
lean_ctor_set(x_20, 1, x_5);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_20);
if (lean_is_scalar(x_19)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_19;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 3);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_20);
lean_inc_ref(x_5);
x_30 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_5);
lean_ctor_set(x_30, 2, x_5);
lean_ctor_set(x_30, 3, x_29);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
if (lean_is_scalar(x_19)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_19;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_21);
return x_32;
}
}
block_62:
{
lean_object* x_36; uint64_t x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_20, 0);
x_37 = lean_ctor_get_uint64(x_36, sizeof(void*)*1);
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get_uint8(x_34, sizeof(void*)*3);
x_40 = lean_ctor_get(x_34, 1);
x_41 = lean_ctor_get(x_34, 2);
lean_inc_ref(x_5);
x_42 = l_Lake_writeFileHash(x_5, x_37);
if (lean_obj_tag(x_42) == 0)
{
lean_dec_ref(x_42);
x_21 = x_34;
x_22 = lean_box(0);
goto block_33;
}
else
{
uint8_t x_43; 
lean_inc(x_41);
lean_inc_ref(x_40);
lean_inc_ref(x_38);
lean_dec(x_20);
lean_dec(x_19);
lean_dec_ref(x_5);
x_43 = !lean_is_exclusive(x_34);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = lean_ctor_get(x_34, 2);
lean_dec(x_44);
x_45 = lean_ctor_get(x_34, 1);
lean_dec(x_45);
x_46 = lean_ctor_get(x_34, 0);
lean_dec(x_46);
x_47 = lean_ctor_get(x_42, 0);
lean_inc(x_47);
lean_dec_ref(x_42);
x_48 = lean_io_error_to_string(x_47);
x_49 = 3;
x_50 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_49);
x_51 = lean_array_get_size(x_38);
x_52 = lean_array_push(x_38, x_50);
lean_ctor_set(x_34, 0, x_52);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_34);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_34);
x_54 = lean_ctor_get(x_42, 0);
lean_inc(x_54);
lean_dec_ref(x_42);
x_55 = lean_io_error_to_string(x_54);
x_56 = 3;
x_57 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_56);
x_58 = lean_array_get_size(x_38);
x_59 = lean_array_push(x_38, x_57);
x_60 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_40);
lean_ctor_set(x_60, 2, x_41);
lean_ctor_set_uint8(x_60, sizeof(void*)*3, x_39);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
block_142:
{
if (x_8 == 0)
{
lean_object* x_65; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec_ref(x_5);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_17);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
else
{
uint8_t x_66; 
lean_dec_ref(x_17);
x_66 = l_System_FilePath_pathExists(x_5);
if (x_66 == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_63);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_68 = lean_ctor_get(x_63, 0);
x_69 = l_Lake_buildArtifactUnlessUpToDate___lam__0___closed__0;
x_70 = lean_string_append(x_69, x_5);
x_71 = 0;
x_72 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set_uint8(x_72, sizeof(void*)*1, x_71);
x_73 = lean_array_push(x_68, x_72);
lean_inc_ref(x_5);
x_74 = l_Lake_createParentDirs(x_5);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec_ref(x_74);
x_75 = lean_ctor_get(x_20, 1);
x_76 = l_Lake_copyFile(x_75, x_5);
if (lean_obj_tag(x_76) == 0)
{
lean_dec_ref(x_76);
if (x_6 == 0)
{
lean_ctor_set(x_63, 0, x_73);
x_34 = x_63;
x_35 = lean_box(0);
goto block_62;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_77, 0, x_6);
lean_ctor_set_uint8(x_77, 1, x_6);
lean_ctor_set_uint8(x_77, 2, x_6);
lean_inc_ref_n(x_77, 2);
x_78 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_77);
lean_ctor_set(x_78, 2, x_77);
x_79 = l_IO_setAccessRights(x_5, x_78);
lean_dec_ref(x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_dec_ref(x_79);
lean_ctor_set(x_63, 0, x_73);
x_34 = x_63;
x_35 = lean_box(0);
goto block_62;
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec_ref(x_5);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec_ref(x_79);
x_81 = lean_io_error_to_string(x_80);
x_82 = 3;
x_83 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set_uint8(x_83, sizeof(void*)*1, x_82);
x_84 = lean_array_get_size(x_73);
x_85 = lean_array_push(x_73, x_83);
lean_ctor_set(x_63, 0, x_85);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_63);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec_ref(x_5);
x_87 = lean_ctor_get(x_76, 0);
lean_inc(x_87);
lean_dec_ref(x_76);
x_88 = lean_io_error_to_string(x_87);
x_89 = 3;
x_90 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set_uint8(x_90, sizeof(void*)*1, x_89);
x_91 = lean_array_get_size(x_73);
x_92 = lean_array_push(x_73, x_90);
lean_ctor_set(x_63, 0, x_92);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_63);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec_ref(x_5);
x_94 = lean_ctor_get(x_74, 0);
lean_inc(x_94);
lean_dec_ref(x_74);
x_95 = lean_io_error_to_string(x_94);
x_96 = 3;
x_97 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set_uint8(x_97, sizeof(void*)*1, x_96);
x_98 = lean_array_get_size(x_73);
x_99 = lean_array_push(x_73, x_97);
lean_ctor_set(x_63, 0, x_99);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_63);
return x_100;
}
}
else
{
lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_101 = lean_ctor_get(x_63, 0);
x_102 = lean_ctor_get_uint8(x_63, sizeof(void*)*3);
x_103 = lean_ctor_get(x_63, 1);
x_104 = lean_ctor_get(x_63, 2);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_101);
lean_dec(x_63);
x_105 = l_Lake_buildArtifactUnlessUpToDate___lam__0___closed__0;
x_106 = lean_string_append(x_105, x_5);
x_107 = 0;
x_108 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set_uint8(x_108, sizeof(void*)*1, x_107);
x_109 = lean_array_push(x_101, x_108);
lean_inc_ref(x_5);
x_110 = l_Lake_createParentDirs(x_5);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; 
lean_dec_ref(x_110);
x_111 = lean_ctor_get(x_20, 1);
x_112 = l_Lake_copyFile(x_111, x_5);
if (lean_obj_tag(x_112) == 0)
{
lean_dec_ref(x_112);
if (x_6 == 0)
{
lean_object* x_113; 
x_113 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_113, 0, x_109);
lean_ctor_set(x_113, 1, x_103);
lean_ctor_set(x_113, 2, x_104);
lean_ctor_set_uint8(x_113, sizeof(void*)*3, x_102);
x_34 = x_113;
x_35 = lean_box(0);
goto block_62;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_114, 0, x_6);
lean_ctor_set_uint8(x_114, 1, x_6);
lean_ctor_set_uint8(x_114, 2, x_6);
lean_inc_ref_n(x_114, 2);
x_115 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set(x_115, 2, x_114);
x_116 = l_IO_setAccessRights(x_5, x_115);
lean_dec_ref(x_115);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; 
lean_dec_ref(x_116);
x_117 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_117, 0, x_109);
lean_ctor_set(x_117, 1, x_103);
lean_ctor_set(x_117, 2, x_104);
lean_ctor_set_uint8(x_117, sizeof(void*)*3, x_102);
x_34 = x_117;
x_35 = lean_box(0);
goto block_62;
}
else
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec_ref(x_5);
x_118 = lean_ctor_get(x_116, 0);
lean_inc(x_118);
lean_dec_ref(x_116);
x_119 = lean_io_error_to_string(x_118);
x_120 = 3;
x_121 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set_uint8(x_121, sizeof(void*)*1, x_120);
x_122 = lean_array_get_size(x_109);
x_123 = lean_array_push(x_109, x_121);
x_124 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_103);
lean_ctor_set(x_124, 2, x_104);
lean_ctor_set_uint8(x_124, sizeof(void*)*3, x_102);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec_ref(x_5);
x_126 = lean_ctor_get(x_112, 0);
lean_inc(x_126);
lean_dec_ref(x_112);
x_127 = lean_io_error_to_string(x_126);
x_128 = 3;
x_129 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set_uint8(x_129, sizeof(void*)*1, x_128);
x_130 = lean_array_get_size(x_109);
x_131 = lean_array_push(x_109, x_129);
x_132 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_103);
lean_ctor_set(x_132, 2, x_104);
lean_ctor_set_uint8(x_132, sizeof(void*)*3, x_102);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
else
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec_ref(x_5);
x_134 = lean_ctor_get(x_110, 0);
lean_inc(x_134);
lean_dec_ref(x_110);
x_135 = lean_io_error_to_string(x_134);
x_136 = 3;
x_137 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set_uint8(x_137, sizeof(void*)*1, x_136);
x_138 = lean_array_get_size(x_109);
x_139 = lean_array_push(x_109, x_137);
x_140 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_103);
lean_ctor_set(x_140, 2, x_104);
lean_ctor_set_uint8(x_140, sizeof(void*)*3, x_102);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
else
{
x_21 = x_63;
x_22 = lean_box(0);
goto block_33;
}
}
}
}
else
{
uint8_t x_213; 
lean_dec(x_17);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
x_213 = !lean_is_exclusive(x_16);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_16, 0);
lean_dec(x_214);
x_215 = lean_box(0);
lean_ctor_set(x_16, 0, x_215);
return x_16;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_16, 1);
lean_inc(x_216);
lean_dec(x_16);
x_217 = lean_box(0);
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_216);
return x_218;
}
}
}
else
{
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint64_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_17 = lean_unbox(x_6);
x_18 = lean_unbox(x_8);
x_19 = l_Lake_buildArtifactUnlessUpToDate___lam__0(x_16, x_2, x_3, x_4, x_5, x_17, x_7, x_18, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, uint64_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
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
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__1___boxed(lean_object** _args) {
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
x_23 = l_Lake_buildArtifactUnlessUpToDate___lam__1(x_18, x_2, x_3, x_19, x_20, x_21, x_7, x_8, x_22, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_37; 
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
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint64_t x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_91; uint8_t x_95; uint8_t x_124; uint8_t x_125; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
x_45 = lean_ctor_get(x_8, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_39);
lean_ctor_set(x_12, 0, x_44);
x_47 = l_Lake_Package_isArtifactCacheEnabled___at___00Lake_buildArtifactUnlessUpToDate_spec__0___redArg(x_45, x_11, x_12);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec_ref(x_47);
x_50 = lean_ctor_get(x_46, 2);
x_51 = lean_ctor_get_uint64(x_39, sizeof(void*)*3);
x_52 = lean_ctor_get(x_39, 2);
x_124 = 1;
x_125 = lean_unbox(x_48);
lean_dec(x_48);
if (x_125 == 0)
{
lean_object* x_126; 
lean_inc(x_43);
x_126 = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(x_7, x_1, x_39, x_43, x_52, x_8, x_9, x_10, x_11, x_49);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; uint8_t x_130; uint8_t x_131; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec_ref(x_126);
x_129 = 0;
x_130 = lean_unbox(x_127);
lean_dec(x_127);
x_131 = l_Lake_instDecidableEqOutputStatus(x_130, x_129);
if (x_131 == 0)
{
lean_object* x_132; 
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec_ref(x_39);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_132 = l_Lake_computeArtifact___redArg(x_1, x_4, x_3, x_11, x_128);
lean_dec_ref(x_11);
x_91 = x_132;
goto block_94;
}
else
{
lean_object* x_133; 
lean_inc_ref(x_11);
lean_inc_ref(x_41);
lean_inc_ref(x_1);
lean_inc(x_45);
lean_inc_ref(x_50);
x_133 = l_Lake_buildArtifactUnlessUpToDate___lam__0(x_51, x_43, x_50, x_45, x_1, x_6, x_41, x_124, x_7, x_8, x_9, x_10, x_11, x_128);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
if (lean_obj_tag(x_134) == 1)
{
lean_object* x_135; lean_object* x_136; 
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
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec_ref(x_133);
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
lean_dec_ref(x_134);
x_66 = x_136;
x_67 = x_135;
x_68 = lean_box(0);
goto block_90;
}
else
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_134);
x_137 = lean_ctor_get(x_133, 1);
lean_inc(x_137);
lean_dec_ref(x_133);
x_138 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_3, x_4, x_39, x_41, x_7, x_8, x_9, x_10, x_11, x_137);
lean_dec_ref(x_39);
x_91 = x_138;
goto block_94;
}
}
else
{
uint8_t x_139; 
lean_dec(x_45);
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
x_139 = !lean_is_exclusive(x_133);
if (x_139 == 0)
{
return x_133;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_133, 0);
x_141 = lean_ctor_get(x_133, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_133);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
}
else
{
uint8_t x_143; 
lean_dec(x_45);
lean_dec(x_43);
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
x_143 = !lean_is_exclusive(x_126);
if (x_143 == 0)
{
return x_126;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_126, 0);
x_145 = lean_ctor_get(x_126, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_126);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
else
{
lean_inc_ref(x_50);
if (x_5 == 0)
{
lean_object* x_147; uint8_t x_148; 
x_147 = lean_ctor_get(x_45, 6);
x_148 = lean_ctor_get_uint8(x_147, sizeof(void*)*26 + 4);
x_95 = x_148;
goto block_123;
}
else
{
x_95 = x_124;
goto block_123;
}
}
block_65:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec_ref(x_58);
x_62 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = l_Lake_CacheMap_insertCore(x_51, x_62, x_55);
x_64 = lean_st_ref_set(x_54, x_63);
lean_dec(x_54);
x_14 = x_56;
x_15 = x_57;
x_16 = x_53;
x_17 = x_59;
x_18 = lean_box(0);
goto block_22;
}
block_90:
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_45, 23);
lean_inc(x_69);
lean_dec(x_45);
if (lean_obj_tag(x_69) == 1)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; uint64_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
x_71 = lean_st_ref_take(x_70);
x_72 = lean_ctor_get(x_66, 0);
x_73 = lean_ctor_get(x_67, 0);
lean_inc_ref(x_73);
x_74 = lean_ctor_get_uint8(x_67, sizeof(void*)*3);
x_75 = lean_ctor_get(x_67, 1);
lean_inc_ref(x_75);
x_76 = lean_ctor_get(x_67, 2);
lean_inc(x_76);
lean_dec_ref(x_67);
x_77 = lean_ctor_get_uint64(x_72, sizeof(void*)*1);
x_78 = lean_ctor_get(x_72, 0);
x_79 = lean_string_utf8_byte_size(x_78);
x_80 = lean_unsigned_to_nat(0u);
x_81 = lean_nat_dec_eq(x_79, x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = l_Lake_Hash_hex(x_77);
x_83 = l_Lake_instToOutputJsonArtifact___lam__0___closed__0;
x_84 = lean_string_append(x_82, x_83);
x_85 = lean_string_append(x_84, x_78);
x_53 = x_74;
x_54 = x_70;
x_55 = x_71;
x_56 = x_66;
x_57 = x_73;
x_58 = x_75;
x_59 = x_76;
x_60 = lean_box(0);
x_61 = x_85;
goto block_65;
}
else
{
lean_object* x_86; 
x_86 = l_Lake_Hash_hex(x_77);
x_53 = x_74;
x_54 = x_70;
x_55 = x_71;
x_56 = x_66;
x_57 = x_73;
x_58 = x_75;
x_59 = x_76;
x_60 = lean_box(0);
x_61 = x_86;
goto block_65;
}
}
else
{
lean_object* x_87; uint8_t x_88; lean_object* x_89; 
lean_dec(x_69);
x_87 = lean_ctor_get(x_67, 0);
lean_inc_ref(x_87);
x_88 = lean_ctor_get_uint8(x_67, sizeof(void*)*3);
x_89 = lean_ctor_get(x_67, 2);
lean_inc(x_89);
lean_dec_ref(x_67);
x_14 = x_66;
x_15 = x_87;
x_16 = x_88;
x_17 = x_89;
x_18 = lean_box(0);
goto block_22;
}
}
block_94:
{
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec_ref(x_91);
x_66 = x_92;
x_67 = x_93;
x_68 = lean_box(0);
goto block_90;
}
else
{
lean_dec(x_45);
return x_91;
}
}
block_123:
{
lean_object* x_96; 
lean_inc_ref(x_11);
lean_inc_ref(x_41);
lean_inc_ref(x_1);
lean_inc(x_45);
lean_inc_ref(x_50);
lean_inc(x_43);
x_96 = l_Lake_buildArtifactUnlessUpToDate___lam__0(x_51, x_43, x_50, x_45, x_1, x_6, x_41, x_95, x_7, x_8, x_9, x_10, x_11, x_49);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
if (lean_obj_tag(x_97) == 1)
{
lean_object* x_98; lean_object* x_99; 
lean_dec_ref(x_50);
lean_dec(x_43);
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
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec_ref(x_96);
x_99 = lean_ctor_get(x_97, 0);
lean_inc(x_99);
lean_dec_ref(x_97);
x_66 = x_99;
x_67 = x_98;
x_68 = lean_box(0);
goto block_90;
}
else
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_97);
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
lean_dec_ref(x_96);
x_101 = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(x_7, x_1, x_39, x_43, x_52, x_8, x_9, x_10, x_11, x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_105; uint8_t x_106; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec_ref(x_101);
x_104 = 0;
x_105 = lean_unbox(x_102);
x_106 = l_Lake_instDecidableEqOutputStatus(x_105, x_104);
if (x_106 == 0)
{
lean_object* x_107; uint8_t x_108; lean_object* x_109; 
lean_dec_ref(x_41);
lean_dec_ref(x_39);
lean_dec_ref(x_2);
x_107 = lean_box(0);
x_108 = lean_unbox(x_102);
lean_dec(x_102);
lean_inc(x_45);
x_109 = l_Lake_buildArtifactUnlessUpToDate___lam__1(x_108, x_1, x_4, x_3, x_6, x_95, x_45, x_50, x_51, x_107, x_7, x_8, x_9, x_10, x_11, x_103);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_91 = x_109;
goto block_94;
}
else
{
lean_object* x_110; 
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_4);
lean_inc_ref(x_1);
x_110 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_3, x_4, x_39, x_41, x_7, x_8, x_9, x_10, x_11, x_103);
lean_dec_ref(x_39);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; 
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec_ref(x_110);
x_112 = lean_box(0);
x_113 = lean_unbox(x_102);
lean_dec(x_102);
lean_inc(x_45);
x_114 = l_Lake_buildArtifactUnlessUpToDate___lam__1(x_113, x_1, x_4, x_3, x_6, x_95, x_45, x_50, x_51, x_112, x_7, x_8, x_9, x_10, x_11, x_111);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_91 = x_114;
goto block_94;
}
else
{
lean_dec(x_102);
lean_dec_ref(x_50);
lean_dec(x_45);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_110;
}
}
}
else
{
uint8_t x_115; 
lean_dec_ref(x_50);
lean_dec(x_45);
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
x_115 = !lean_is_exclusive(x_101);
if (x_115 == 0)
{
return x_101;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_101, 0);
x_117 = lean_ctor_get(x_101, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_101);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
}
else
{
uint8_t x_119; 
lean_dec_ref(x_50);
lean_dec(x_45);
lean_dec(x_43);
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
x_119 = !lean_is_exclusive(x_96);
if (x_119 == 0)
{
return x_96;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_96, 0);
x_121 = lean_ctor_get(x_96, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_96);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_149 = lean_ctor_get(x_42, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_42, 1);
lean_inc(x_150);
lean_dec_ref(x_42);
x_151 = lean_ctor_get(x_39, 2);
lean_inc_ref(x_39);
lean_ctor_set(x_12, 0, x_150);
x_152 = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(x_7, x_1, x_39, x_149, x_151, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; uint8_t x_156; uint8_t x_157; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec_ref(x_152);
x_155 = 0;
x_156 = lean_unbox(x_153);
lean_dec(x_153);
x_157 = l_Lake_instDecidableEqOutputStatus(x_156, x_155);
if (x_157 == 0)
{
lean_object* x_158; 
lean_dec_ref(x_41);
lean_dec_ref(x_39);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_158 = l_Lake_computeArtifact___redArg(x_1, x_4, x_3, x_11, x_154);
lean_dec_ref(x_11);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec_ref(x_158);
x_23 = x_159;
x_24 = x_160;
x_25 = lean_box(0);
goto block_36;
}
else
{
return x_158;
}
}
else
{
lean_object* x_161; 
x_161 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_3, x_4, x_39, x_41, x_7, x_8, x_9, x_10, x_11, x_154);
lean_dec_ref(x_39);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec_ref(x_161);
x_23 = x_162;
x_24 = x_163;
x_25 = lean_box(0);
goto block_36;
}
else
{
return x_161;
}
}
}
else
{
uint8_t x_164; 
lean_dec_ref(x_41);
lean_dec_ref(x_39);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_164 = !lean_is_exclusive(x_152);
if (x_164 == 0)
{
return x_152;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_152, 0);
x_166 = lean_ctor_get(x_152, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_152);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
}
else
{
uint8_t x_168; 
lean_dec_ref(x_41);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_168 = !lean_is_exclusive(x_42);
if (x_168 == 0)
{
lean_object* x_169; 
x_169 = lean_ctor_get(x_42, 1);
lean_ctor_set(x_12, 0, x_169);
lean_ctor_set(x_42, 1, x_12);
return x_42;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_42, 0);
x_171 = lean_ctor_get(x_42, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_42);
lean_ctor_set(x_12, 0, x_171);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_12);
return x_172;
}
}
}
else
{
lean_object* x_173; uint8_t x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_173 = lean_ctor_get(x_12, 0);
x_174 = lean_ctor_get_uint8(x_12, sizeof(void*)*3);
x_175 = lean_ctor_get(x_12, 1);
x_176 = lean_ctor_get(x_12, 2);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_173);
lean_dec(x_12);
x_177 = l_Lake_buildFileUnlessUpToDate_x27___closed__0;
lean_inc_ref(x_1);
x_178 = lean_string_append(x_1, x_177);
lean_inc_ref(x_178);
x_179 = l_Lake_readTraceFile(x_178, x_173);
if (lean_obj_tag(x_179) == 0)
{
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint64_t x_189; lean_object* x_190; uint8_t x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_229; uint8_t x_233; uint8_t x_262; uint8_t x_263; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec_ref(x_179);
x_182 = lean_ctor_get(x_8, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_175);
x_184 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_175);
lean_ctor_set(x_184, 2, x_176);
lean_ctor_set_uint8(x_184, sizeof(void*)*3, x_174);
x_185 = l_Lake_Package_isArtifactCacheEnabled___at___00Lake_buildArtifactUnlessUpToDate_spec__0___redArg(x_182, x_11, x_184);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec_ref(x_185);
x_188 = lean_ctor_get(x_183, 2);
x_189 = lean_ctor_get_uint64(x_175, sizeof(void*)*3);
x_190 = lean_ctor_get(x_175, 2);
x_262 = 1;
x_263 = lean_unbox(x_186);
lean_dec(x_186);
if (x_263 == 0)
{
lean_object* x_264; 
lean_inc(x_180);
x_264 = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(x_7, x_1, x_175, x_180, x_190, x_8, x_9, x_10, x_11, x_187);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; uint8_t x_267; uint8_t x_268; uint8_t x_269; 
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec_ref(x_264);
x_267 = 0;
x_268 = lean_unbox(x_265);
lean_dec(x_265);
x_269 = l_Lake_instDecidableEqOutputStatus(x_268, x_267);
if (x_269 == 0)
{
lean_object* x_270; 
lean_dec(x_180);
lean_dec_ref(x_178);
lean_dec_ref(x_175);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_270 = l_Lake_computeArtifact___redArg(x_1, x_4, x_3, x_11, x_266);
lean_dec_ref(x_11);
x_229 = x_270;
goto block_232;
}
else
{
lean_object* x_271; 
lean_inc_ref(x_11);
lean_inc_ref(x_178);
lean_inc_ref(x_1);
lean_inc(x_182);
lean_inc_ref(x_188);
x_271 = l_Lake_buildArtifactUnlessUpToDate___lam__0(x_189, x_180, x_188, x_182, x_1, x_6, x_178, x_262, x_7, x_8, x_9, x_10, x_11, x_266);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
if (lean_obj_tag(x_272) == 1)
{
lean_object* x_273; lean_object* x_274; 
lean_dec_ref(x_178);
lean_dec_ref(x_175);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec_ref(x_271);
x_274 = lean_ctor_get(x_272, 0);
lean_inc(x_274);
lean_dec_ref(x_272);
x_204 = x_274;
x_205 = x_273;
x_206 = lean_box(0);
goto block_228;
}
else
{
lean_object* x_275; lean_object* x_276; 
lean_dec(x_272);
x_275 = lean_ctor_get(x_271, 1);
lean_inc(x_275);
lean_dec_ref(x_271);
x_276 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_3, x_4, x_175, x_178, x_7, x_8, x_9, x_10, x_11, x_275);
lean_dec_ref(x_175);
x_229 = x_276;
goto block_232;
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_182);
lean_dec_ref(x_178);
lean_dec_ref(x_175);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_277 = lean_ctor_get(x_271, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_271, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_279 = x_271;
} else {
 lean_dec_ref(x_271);
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
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_182);
lean_dec(x_180);
lean_dec_ref(x_178);
lean_dec_ref(x_175);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_281 = lean_ctor_get(x_264, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_264, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 x_283 = x_264;
} else {
 lean_dec_ref(x_264);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(1, 2, 0);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_281);
lean_ctor_set(x_284, 1, x_282);
return x_284;
}
}
else
{
lean_inc_ref(x_188);
if (x_5 == 0)
{
lean_object* x_285; uint8_t x_286; 
x_285 = lean_ctor_get(x_182, 6);
x_286 = lean_ctor_get_uint8(x_285, sizeof(void*)*26 + 4);
x_233 = x_286;
goto block_261;
}
else
{
x_233 = x_262;
goto block_261;
}
}
block_203:
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec_ref(x_196);
x_200 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_200, 0, x_199);
x_201 = l_Lake_CacheMap_insertCore(x_189, x_200, x_193);
x_202 = lean_st_ref_set(x_192, x_201);
lean_dec(x_192);
x_14 = x_194;
x_15 = x_195;
x_16 = x_191;
x_17 = x_197;
x_18 = lean_box(0);
goto block_22;
}
block_228:
{
lean_object* x_207; 
x_207 = lean_ctor_get(x_182, 23);
lean_inc(x_207);
lean_dec(x_182);
if (lean_obj_tag(x_207) == 1)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; lean_object* x_213; lean_object* x_214; uint64_t x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
lean_dec_ref(x_207);
x_209 = lean_st_ref_take(x_208);
x_210 = lean_ctor_get(x_204, 0);
x_211 = lean_ctor_get(x_205, 0);
lean_inc_ref(x_211);
x_212 = lean_ctor_get_uint8(x_205, sizeof(void*)*3);
x_213 = lean_ctor_get(x_205, 1);
lean_inc_ref(x_213);
x_214 = lean_ctor_get(x_205, 2);
lean_inc(x_214);
lean_dec_ref(x_205);
x_215 = lean_ctor_get_uint64(x_210, sizeof(void*)*1);
x_216 = lean_ctor_get(x_210, 0);
x_217 = lean_string_utf8_byte_size(x_216);
x_218 = lean_unsigned_to_nat(0u);
x_219 = lean_nat_dec_eq(x_217, x_218);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_220 = l_Lake_Hash_hex(x_215);
x_221 = l_Lake_instToOutputJsonArtifact___lam__0___closed__0;
x_222 = lean_string_append(x_220, x_221);
x_223 = lean_string_append(x_222, x_216);
x_191 = x_212;
x_192 = x_208;
x_193 = x_209;
x_194 = x_204;
x_195 = x_211;
x_196 = x_213;
x_197 = x_214;
x_198 = lean_box(0);
x_199 = x_223;
goto block_203;
}
else
{
lean_object* x_224; 
x_224 = l_Lake_Hash_hex(x_215);
x_191 = x_212;
x_192 = x_208;
x_193 = x_209;
x_194 = x_204;
x_195 = x_211;
x_196 = x_213;
x_197 = x_214;
x_198 = lean_box(0);
x_199 = x_224;
goto block_203;
}
}
else
{
lean_object* x_225; uint8_t x_226; lean_object* x_227; 
lean_dec(x_207);
x_225 = lean_ctor_get(x_205, 0);
lean_inc_ref(x_225);
x_226 = lean_ctor_get_uint8(x_205, sizeof(void*)*3);
x_227 = lean_ctor_get(x_205, 2);
lean_inc(x_227);
lean_dec_ref(x_205);
x_14 = x_204;
x_15 = x_225;
x_16 = x_226;
x_17 = x_227;
x_18 = lean_box(0);
goto block_22;
}
}
block_232:
{
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec_ref(x_229);
x_204 = x_230;
x_205 = x_231;
x_206 = lean_box(0);
goto block_228;
}
else
{
lean_dec(x_182);
return x_229;
}
}
block_261:
{
lean_object* x_234; 
lean_inc_ref(x_11);
lean_inc_ref(x_178);
lean_inc_ref(x_1);
lean_inc(x_182);
lean_inc_ref(x_188);
lean_inc(x_180);
x_234 = l_Lake_buildArtifactUnlessUpToDate___lam__0(x_189, x_180, x_188, x_182, x_1, x_6, x_178, x_233, x_7, x_8, x_9, x_10, x_11, x_187);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
if (lean_obj_tag(x_235) == 1)
{
lean_object* x_236; lean_object* x_237; 
lean_dec_ref(x_188);
lean_dec(x_180);
lean_dec_ref(x_178);
lean_dec_ref(x_175);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec_ref(x_234);
x_237 = lean_ctor_get(x_235, 0);
lean_inc(x_237);
lean_dec_ref(x_235);
x_204 = x_237;
x_205 = x_236;
x_206 = lean_box(0);
goto block_228;
}
else
{
lean_object* x_238; lean_object* x_239; 
lean_dec(x_235);
x_238 = lean_ctor_get(x_234, 1);
lean_inc(x_238);
lean_dec_ref(x_234);
x_239 = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(x_7, x_1, x_175, x_180, x_190, x_8, x_9, x_10, x_11, x_238);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; uint8_t x_242; uint8_t x_243; uint8_t x_244; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
lean_dec_ref(x_239);
x_242 = 0;
x_243 = lean_unbox(x_240);
x_244 = l_Lake_instDecidableEqOutputStatus(x_243, x_242);
if (x_244 == 0)
{
lean_object* x_245; uint8_t x_246; lean_object* x_247; 
lean_dec_ref(x_178);
lean_dec_ref(x_175);
lean_dec_ref(x_2);
x_245 = lean_box(0);
x_246 = lean_unbox(x_240);
lean_dec(x_240);
lean_inc(x_182);
x_247 = l_Lake_buildArtifactUnlessUpToDate___lam__1(x_246, x_1, x_4, x_3, x_6, x_233, x_182, x_188, x_189, x_245, x_7, x_8, x_9, x_10, x_11, x_241);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_229 = x_247;
goto block_232;
}
else
{
lean_object* x_248; 
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_4);
lean_inc_ref(x_1);
x_248 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_3, x_4, x_175, x_178, x_7, x_8, x_9, x_10, x_11, x_241);
lean_dec_ref(x_175);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; uint8_t x_251; lean_object* x_252; 
x_249 = lean_ctor_get(x_248, 1);
lean_inc(x_249);
lean_dec_ref(x_248);
x_250 = lean_box(0);
x_251 = lean_unbox(x_240);
lean_dec(x_240);
lean_inc(x_182);
x_252 = l_Lake_buildArtifactUnlessUpToDate___lam__1(x_251, x_1, x_4, x_3, x_6, x_233, x_182, x_188, x_189, x_250, x_7, x_8, x_9, x_10, x_11, x_249);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_229 = x_252;
goto block_232;
}
else
{
lean_dec(x_240);
lean_dec_ref(x_188);
lean_dec(x_182);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_248;
}
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec_ref(x_188);
lean_dec(x_182);
lean_dec_ref(x_178);
lean_dec_ref(x_175);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_253 = lean_ctor_get(x_239, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_239, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_255 = x_239;
} else {
 lean_dec_ref(x_239);
 x_255 = lean_box(0);
}
if (lean_is_scalar(x_255)) {
 x_256 = lean_alloc_ctor(1, 2, 0);
} else {
 x_256 = x_255;
}
lean_ctor_set(x_256, 0, x_253);
lean_ctor_set(x_256, 1, x_254);
return x_256;
}
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec_ref(x_188);
lean_dec(x_182);
lean_dec(x_180);
lean_dec_ref(x_178);
lean_dec_ref(x_175);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_257 = lean_ctor_get(x_234, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_234, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_259 = x_234;
} else {
 lean_dec_ref(x_234);
 x_259 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_260 = lean_alloc_ctor(1, 2, 0);
} else {
 x_260 = x_259;
}
lean_ctor_set(x_260, 0, x_257);
lean_ctor_set(x_260, 1, x_258);
return x_260;
}
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_287 = lean_ctor_get(x_179, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_179, 1);
lean_inc(x_288);
lean_dec_ref(x_179);
x_289 = lean_ctor_get(x_175, 2);
lean_inc_ref(x_175);
x_290 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_290, 0, x_288);
lean_ctor_set(x_290, 1, x_175);
lean_ctor_set(x_290, 2, x_176);
lean_ctor_set_uint8(x_290, sizeof(void*)*3, x_174);
x_291 = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00Lake_buildFileUnlessUpToDate_x27_spec__0(x_7, x_1, x_175, x_287, x_289, x_8, x_9, x_10, x_11, x_290);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; uint8_t x_294; uint8_t x_295; uint8_t x_296; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_291, 1);
lean_inc(x_293);
lean_dec_ref(x_291);
x_294 = 0;
x_295 = lean_unbox(x_292);
lean_dec(x_292);
x_296 = l_Lake_instDecidableEqOutputStatus(x_295, x_294);
if (x_296 == 0)
{
lean_object* x_297; 
lean_dec_ref(x_178);
lean_dec_ref(x_175);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_297 = l_Lake_computeArtifact___redArg(x_1, x_4, x_3, x_11, x_293);
lean_dec_ref(x_11);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; lean_object* x_299; 
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_297, 1);
lean_inc(x_299);
lean_dec_ref(x_297);
x_23 = x_298;
x_24 = x_299;
x_25 = lean_box(0);
goto block_36;
}
else
{
return x_297;
}
}
else
{
lean_object* x_300; 
x_300 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_3, x_4, x_175, x_178, x_7, x_8, x_9, x_10, x_11, x_293);
lean_dec_ref(x_175);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; lean_object* x_302; 
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
lean_dec_ref(x_300);
x_23 = x_301;
x_24 = x_302;
x_25 = lean_box(0);
goto block_36;
}
else
{
return x_300;
}
}
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec_ref(x_178);
lean_dec_ref(x_175);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_303 = lean_ctor_get(x_291, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_291, 1);
lean_inc(x_304);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 x_305 = x_291;
} else {
 lean_dec_ref(x_291);
 x_305 = lean_box(0);
}
if (lean_is_scalar(x_305)) {
 x_306 = lean_alloc_ctor(1, 2, 0);
} else {
 x_306 = x_305;
}
lean_ctor_set(x_306, 0, x_303);
lean_ctor_set(x_306, 1, x_304);
return x_306;
}
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
lean_dec_ref(x_178);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_307 = lean_ctor_get(x_179, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_179, 1);
lean_inc(x_308);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_309 = x_179;
} else {
 lean_dec_ref(x_179);
 x_309 = lean_box(0);
}
x_310 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set(x_310, 1, x_175);
lean_ctor_set(x_310, 2, x_176);
lean_ctor_set_uint8(x_310, sizeof(void*)*3, x_174);
if (lean_is_scalar(x_309)) {
 x_311 = lean_alloc_ctor(1, 2, 0);
} else {
 x_311 = x_309;
}
lean_ctor_set(x_311, 0, x_307);
lean_ctor_set(x_311, 1, x_310);
return x_311;
}
}
block_22:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_Lake_Artifact_trace(x_14);
x_20 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*3, x_16);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
block_36:
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_24, 1);
lean_dec(x_27);
x_28 = l_Lake_Artifact_trace(x_23);
lean_ctor_set(x_24, 1, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
return x_29;
}
else
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get_uint8(x_24, sizeof(void*)*3);
x_32 = lean_ctor_get(x_24, 2);
lean_inc(x_32);
lean_inc(x_30);
lean_dec(x_24);
x_33 = l_Lake_Artifact_trace(x_23);
x_34 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*3, x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_23);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
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
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
x_14 = l_Lake_buildFileAfterDep___redArg___lam__0(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
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
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
x_14 = l_Lake_buildFileAfterDep___redArg(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
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
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_6);
x_15 = l_Lake_buildFileAfterDep(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(lean_object* x_1) {
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
x_9 = l_Lake_platformTrace___closed__2;
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
x_14 = l_Lake_platformTrace___closed__2;
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
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(x_1);
return x_3;
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
x_12 = l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(x_1);
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
x_26 = l_Lake_BuildTrace_compute___at___00Lake_inputBinFile_spec__0(x_1);
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
static lean_object* _init_l_Lake_inputBinFile___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_alloc_closure((void*)(l_Lake_inputBinFile___redArg___lam__0___boxed), 8, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = l_Lake_instDataKindFilePath;
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lake_inputBinFile___redArg___closed__0;
x_12 = l_Lake_Job_async___redArg(x_9, x_8, x_10, x_11, x_2, x_3, x_4, x_5, x_6);
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
LEAN_EXPORT lean_object* l_Lake_inputBinFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_inputBinFile___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_9;
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
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(lean_object* x_1) {
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
x_9 = l_Lake_platformTrace___closed__2;
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
x_14 = l_Lake_platformTrace___closed__2;
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
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(x_1);
return x_3;
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
x_12 = l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(x_1);
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
x_26 = l_Lake_BuildTrace_compute___at___00Lake_inputTextFile_spec__0(x_1);
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
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_alloc_closure((void*)(l_Lake_inputTextFile___redArg___lam__0___boxed), 8, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = l_Lake_instDataKindFilePath;
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lake_inputBinFile___redArg___closed__0;
x_12 = l_Lake_Job_async___redArg(x_9, x_8, x_10, x_11, x_2, x_3, x_4, x_5, x_6);
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
LEAN_EXPORT lean_object* l_Lake_inputTextFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_inputTextFile___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_9;
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
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lake_inputFile___redArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
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
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_inputDir___lam__0(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
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
lean_inc(x_16);
x_18 = lean_apply_1(x_1, x_16);
x_19 = lean_unbox(x_18);
if (x_19 == 0)
{
lean_dec(x_16);
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
lean_dec(x_16);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(x_1, x_2, x_8, x_9, x_5, x_6);
lean_dec_ref(x_2);
return x_10;
}
}
static lean_object* _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_decidableLT___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_5 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg___closed__0;
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
x_10 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(x_8, x_2, x_7);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
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
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_48; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = lean_unsigned_to_nat(0u);
x_52 = lean_array_get_size(x_37);
x_53 = l_Lake_inputDir___lam__1___closed__0;
x_54 = lean_nat_dec_lt(x_38, x_52);
if (x_54 == 0)
{
lean_dec(x_37);
lean_dec_ref(x_3);
x_39 = x_53;
x_40 = x_9;
x_41 = lean_box(0);
goto block_47;
}
else
{
uint8_t x_55; 
x_55 = lean_nat_dec_le(x_52, x_52);
if (x_55 == 0)
{
if (x_54 == 0)
{
lean_dec(x_37);
lean_dec_ref(x_3);
x_39 = x_53;
x_40 = x_9;
x_41 = lean_box(0);
goto block_47;
}
else
{
size_t x_56; size_t x_57; lean_object* x_58; 
x_56 = 0;
x_57 = lean_usize_of_nat(x_52);
x_58 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(x_3, x_37, x_56, x_57, x_53, x_9);
lean_dec(x_37);
x_48 = x_58;
goto block_51;
}
}
else
{
size_t x_59; size_t x_60; lean_object* x_61; 
x_59 = 0;
x_60 = lean_usize_of_nat(x_52);
x_61 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(x_3, x_37, x_59, x_60, x_53, x_9);
lean_dec(x_37);
x_48 = x_61;
goto block_51;
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
x_24 = x_45;
x_25 = x_39;
x_26 = x_42;
x_27 = lean_box(0);
x_28 = x_40;
x_29 = x_45;
goto block_31;
}
else
{
x_24 = x_45;
x_25 = x_39;
x_26 = x_42;
x_27 = lean_box(0);
x_28 = x_40;
x_29 = x_38;
goto block_31;
}
}
else
{
x_11 = lean_box(0);
x_12 = x_40;
x_13 = x_39;
goto block_15;
}
}
block_51:
{
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec_ref(x_48);
x_39 = x_49;
x_40 = x_50;
x_41 = lean_box(0);
goto block_47;
}
else
{
return x_48;
}
}
}
else
{
uint8_t x_62; 
lean_inc(x_35);
lean_inc_ref(x_34);
lean_inc_ref(x_32);
lean_dec_ref(x_3);
x_62 = !lean_is_exclusive(x_9);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_63 = lean_ctor_get(x_9, 2);
lean_dec(x_63);
x_64 = lean_ctor_get(x_9, 1);
lean_dec(x_64);
x_65 = lean_ctor_get(x_9, 0);
lean_dec(x_65);
x_66 = lean_ctor_get(x_36, 0);
lean_inc(x_66);
lean_dec_ref(x_36);
x_67 = lean_io_error_to_string(x_66);
x_68 = 3;
x_69 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set_uint8(x_69, sizeof(void*)*1, x_68);
x_70 = lean_array_get_size(x_32);
x_71 = lean_array_push(x_32, x_69);
lean_ctor_set(x_9, 0, x_71);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_9);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_9);
x_73 = lean_ctor_get(x_36, 0);
lean_inc(x_73);
lean_dec_ref(x_36);
x_74 = lean_io_error_to_string(x_73);
x_75 = 3;
x_76 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*1, x_75);
x_77 = lean_array_get_size(x_32);
x_78 = lean_array_push(x_32, x_76);
x_79 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_34);
lean_ctor_set(x_79, 2, x_35);
lean_ctor_set_uint8(x_79, sizeof(void*)*3, x_33);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
block_15:
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
block_23:
{
lean_object* x_22; 
lean_dec(x_18);
x_22 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(x_16, x_17, x_21);
lean_dec(x_21);
x_11 = lean_box(0);
x_12 = x_20;
x_13 = x_22;
goto block_15;
}
block_31:
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_29, x_24);
if (x_30 == 0)
{
lean_dec(x_24);
lean_inc(x_29);
x_16 = x_25;
x_17 = x_29;
x_18 = x_26;
x_19 = lean_box(0);
x_20 = x_28;
x_21 = x_29;
goto block_23;
}
else
{
x_16 = x_25;
x_17 = x_29;
x_18 = x_26;
x_19 = lean_box(0);
x_20 = x_28;
x_21 = x_24;
goto block_23;
}
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(uint8_t x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(x_12, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_array_size(x_3);
x_12 = 0;
x_13 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_inputDir_spec__0(x_1, x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
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
else
{
uint8_t x_21; 
lean_dec_ref(x_2);
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
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
x_12 = l_Lake_inputDir___lam__2(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
static lean_object* _init_l_Lake_inputDir___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_inputDir___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_11 = l_Lake_inputDir___closed__0;
lean_inc_ref(x_1);
x_12 = lean_alloc_closure((void*)(l_Lake_inputDir___lam__1___boxed), 10, 3);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
lean_closure_set(x_12, 2, x_3);
x_13 = lean_box(0);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lake_inputBinFile___redArg___closed__0;
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_16 = l_Lake_Job_async___redArg(x_13, x_12, x_14, x_15, x_4, x_5, x_6, x_7, x_8);
x_17 = lean_box(x_2);
x_18 = lean_alloc_closure((void*)(l_Lake_inputDir___lam__2___boxed), 10, 2);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_1);
x_19 = 0;
x_20 = l_Lake_Job_bindM___redArg(x_13, x_16, x_18, x_14, x_19, x_4, x_5, x_6, x_7, x_8, x_9);
return x_20;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg(x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_inputDir_spec__2(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_15;
}
}
LEAN_EXPORT uint64_t l_Lake_buildO___lam__0(uint64_t x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; 
x_3 = l_Lake_Hash_nil;
x_4 = lean_string_hash(x_2);
x_5 = lean_uint64_mix_hash(x_3, x_4);
x_6 = lean_uint64_mix_hash(x_1, x_5);
return x_6;
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
x_1 = l_Lake_Hash_nil;
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
x_83 = l_Lake_Hash_nil;
x_84 = lean_unsigned_to_nat(0u);
x_85 = lean_array_get_size(x_1);
x_86 = lean_nat_dec_lt(x_84, x_85);
if (x_86 == 0)
{
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
if (x_86 == 0)
{
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
x_90 = l_Lake_buildO___lam__2___boxed__const__1;
lean_inc_ref(x_1);
x_91 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_7, x_8, x_1, x_88, x_89, x_90);
x_92 = lean_unbox_uint64(x_91);
lean_dec(x_91);
x_24 = x_92;
goto block_82;
}
}
else
{
size_t x_93; size_t x_94; lean_object* x_95; lean_object* x_96; uint64_t x_97; 
x_93 = 0;
x_94 = lean_usize_of_nat(x_85);
x_95 = l_Lake_buildO___lam__2___boxed__const__1;
lean_inc_ref(x_1);
x_96 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_7, x_8, x_1, x_93, x_94, x_95);
x_97 = lean_unbox_uint64(x_96);
lean_dec(x_96);
x_24 = x_97;
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
x_31 = l_Lake_platformTrace___closed__2;
x_32 = l_Lake_platformTrace___closed__4;
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
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lake_buildO___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
static lean_object* _init_l_Lake_buildO___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_buildO___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_buildO___closed__1() {
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
x_14 = l_Lake_buildO___closed__0;
x_15 = l_Lake_instDataKindFilePath;
x_16 = l_Lake_buildO___closed__1;
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
LEAN_EXPORT lean_object* l_Lake_buildO___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lake_buildO(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
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
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(lean_object* x_1, size_t x_2, size_t x_3, uint64_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; size_t x_11; size_t x_12; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lake_Hash_nil;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(x_1, x_5, x_6, x_7);
lean_dec_ref(x_1);
x_9 = lean_box_uint64(x_8);
return x_9;
}
}
static lean_object* _init_l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
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
x_5 = l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___closed__0;
x_6 = lean_string_append(x_1, x_5);
x_7 = lean_string_append(x_6, x_3);
x_1 = x_7;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_List_toString___at___00Lake_buildLeanO_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[]", 2, 2);
return x_1;
}
}
static lean_object* _init_l_List_toString___at___00Lake_buildLeanO_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_toString___at___00Lake_buildLeanO_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_toString___at___00Lake_buildLeanO_spec__0___closed__0;
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
x_5 = l_List_toString___at___00Lake_buildLeanO_spec__0___closed__1;
x_6 = lean_string_append(x_5, x_4);
x_7 = l_List_toString___at___00Lake_buildLeanO_spec__0___closed__2;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = l_List_toString___at___00Lake_buildLeanO_spec__0___closed__1;
x_11 = lean_string_append(x_10, x_9);
x_12 = l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0(x_11, x_3);
x_13 = 93;
x_14 = lean_string_push(x_12, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanO_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_toString___at___00Lake_buildLeanO_spec__0(x_1);
lean_dec(x_1);
return x_2;
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
x_50 = l_Lake_Hash_nil;
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_array_get_size(x_2);
x_53 = lean_nat_dec_lt(x_51, x_52);
if (x_53 == 0)
{
x_21 = x_50;
goto block_49;
}
else
{
uint8_t x_54; 
x_54 = lean_nat_dec_le(x_52, x_52);
if (x_54 == 0)
{
if (x_53 == 0)
{
x_21 = x_50;
goto block_49;
}
else
{
size_t x_55; size_t x_56; uint64_t x_57; 
x_55 = 0;
x_56 = lean_usize_of_nat(x_52);
x_57 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(x_2, x_55, x_56, x_50);
x_21 = x_57;
goto block_49;
}
}
else
{
size_t x_58; size_t x_59; uint64_t x_60; 
x_58 = 0;
x_59 = lean_usize_of_nat(x_52);
x_60 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(x_2, x_58, x_59, x_50);
x_21 = x_60;
goto block_49;
}
}
block_49:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_22 = l_Lake_buildO___lam__2___closed__0;
x_23 = l_Lake_buildO___lam__2___closed__1;
x_24 = lean_array_to_list(x_2);
x_25 = l_List_toString___at___00Lake_buildLeanO_spec__0(x_24);
lean_dec(x_24);
x_26 = lean_string_append(x_23, x_25);
lean_dec_ref(x_25);
x_27 = lean_string_append(x_22, x_26);
lean_dec_ref(x_26);
x_28 = l_Lake_platformTrace___closed__2;
x_29 = l_Lake_platformTrace___closed__4;
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
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_buildLeanO___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_13 = lean_alloc_closure((void*)(l_Lake_buildLeanO___lam__1___boxed), 12, 4);
lean_closure_set(x_13, 0, x_3);
lean_closure_set(x_13, 1, x_4);
lean_closure_set(x_13, 2, x_1);
lean_closure_set(x_13, 3, x_5);
x_14 = l_Lake_instDataKindFilePath;
x_15 = lean_unsigned_to_nat(0u);
x_16 = 0;
x_17 = l_Lake_Job_mapM___redArg(x_14, x_2, x_13, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11);
return x_17;
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
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
x_12 = l_Lake_buildStaticLib___lam__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_11 = lean_box(x_3);
x_12 = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lam__1___boxed), 10, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
x_13 = l_Lake_instDataKindFilePath;
x_14 = l_Lake_buildStaticLib___closed__0;
x_15 = l_Lake_Job_collectArray___redArg(x_2, x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = 0;
x_18 = l_Lake_Job_mapM___redArg(x_13, x_15, x_12, x_16, x_17, x_4, x_5, x_6, x_7, x_8, x_9);
return x_18;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-l", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-L", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_inc(x_6);
x_16 = l_Lake_Dynlib_dir_x3f(x_6);
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = lean_array_push(x_4, x_19);
x_7 = x_20;
goto block_15;
}
else
{
lean_dec(x_16);
x_7 = x_4;
goto block_15;
}
block_15:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_8);
lean_dec(x_6);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; size_t x_7; lean_object* x_8; 
x_3 = l_Lake_inputDir___lam__1___closed__0;
x_4 = lean_array_size(x_1);
x_5 = 0;
x_6 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(x_1, x_4, x_5, x_3);
x_7 = lean_array_size(x_2);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(x_2, x_7, x_5, x_6);
return x_8;
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
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_12 = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(x_1, x_2, x_8);
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
x_111 = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(x_1, x_2, x_7);
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
x_141 = lean_nat_add(x_138, x_140);
lean_dec(x_140);
lean_dec(x_138);
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
lean_ctor_set(x_143, 3, x_139);
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
x_138 = x_149;
x_139 = x_148;
x_140 = x_150;
goto block_144;
}
else
{
lean_object* x_151; 
x_151 = lean_unsigned_to_nat(0u);
x_138 = x_149;
x_139 = x_148;
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_6);
x_7 = lean_array_push(x_4, x_1);
x_8 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(x_5, x_3);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_List_elem___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(x_5, x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_inc_ref(x_5);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_2);
if (x_8 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
x_27 = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(x_5, x_26, x_3);
x_11 = x_27;
goto block_25;
}
else
{
lean_dec_ref(x_5);
x_11 = x_3;
goto block_25;
}
block_25:
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
if (x_15 == 0)
{
lean_object* x_18; 
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
x_21 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(x_10, x_6, x_19, x_20, x_12);
lean_dec_ref(x_6);
return x_21;
}
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = 0;
x_23 = lean_usize_of_nat(x_14);
x_24 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(x_10, x_6, x_22, x_23, x_12);
lean_dec_ref(x_6);
return x_24;
}
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_2);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_3);
lean_ctor_set(x_30, 1, x_7);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0___closed__0;
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
x_12 = l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0___closed__0;
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
static lean_object* _init_l_Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0___closed__0;
x_3 = lean_box(0);
x_4 = l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0(x_1, x_3);
x_5 = l_String_intercalate(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("library dependency cycle:\n", 26, 26);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_7; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_unsigned_to_nat(0u);
x_36 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1;
x_37 = lean_array_get_size(x_1);
x_38 = lean_nat_dec_lt(x_35, x_37);
if (x_38 == 0)
{
x_4 = x_36;
goto block_6;
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2;
x_40 = lean_nat_dec_le(x_37, x_37);
if (x_40 == 0)
{
if (x_38 == 0)
{
x_4 = x_36;
goto block_6;
}
else
{
size_t x_41; size_t x_42; lean_object* x_43; 
x_41 = 0;
x_42 = lean_usize_of_nat(x_37);
x_43 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(x_1, x_41, x_42, x_39);
x_7 = x_43;
goto block_34;
}
}
else
{
size_t x_44; size_t x_45; lean_object* x_46; 
x_44 = 0;
x_45 = lean_usize_of_nat(x_37);
x_46 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(x_1, x_44, x_45, x_39);
x_7 = x_46;
goto block_34;
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
block_34:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0;
x_12 = l_Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0(x_8);
x_13 = lean_string_append(x_11, x_12);
lean_dec_ref(x_12);
x_14 = 3;
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_14);
x_16 = lean_array_get_size(x_10);
x_17 = lean_array_push(x_10, x_15);
lean_ctor_set(x_2, 0, x_17);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_2);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get(x_2, 2);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_19);
lean_dec(x_2);
x_23 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0;
x_24 = l_Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0(x_8);
x_25 = lean_string_append(x_23, x_24);
lean_dec_ref(x_24);
x_26 = 3;
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
x_28 = lean_array_get_size(x_19);
x_29 = lean_array_push(x_19, x_27);
x_30 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_21);
lean_ctor_set(x_30, 2, x_22);
lean_ctor_set_uint8(x_30, sizeof(void*)*3, x_20);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_7, 0);
lean_inc(x_32);
lean_dec_ref(x_7);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_4 = x_33;
goto block_6;
}
}
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(x_1, x_7);
return x_9;
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
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint64_t x_16; uint64_t x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_132 = l_Lake_Hash_nil;
x_133 = lean_unsigned_to_nat(0u);
x_134 = lean_array_get_size(x_1);
x_135 = lean_nat_dec_lt(x_133, x_134);
if (x_135 == 0)
{
x_16 = x_132;
goto block_131;
}
else
{
uint8_t x_136; 
x_136 = lean_nat_dec_le(x_134, x_134);
if (x_136 == 0)
{
if (x_135 == 0)
{
x_16 = x_132;
goto block_131;
}
else
{
size_t x_137; size_t x_138; uint64_t x_139; 
x_137 = 0;
x_138 = lean_usize_of_nat(x_134);
x_139 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(x_1, x_137, x_138, x_132);
x_16 = x_139;
goto block_131;
}
}
else
{
size_t x_140; size_t x_141; uint64_t x_142; 
x_140 = 0;
x_141 = lean_usize_of_nat(x_134);
x_142 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(x_1, x_140, x_141, x_132);
x_16 = x_142;
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
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lake_platformTrace___closed__2;
x_21 = l_Lake_buildO___lam__2___closed__0;
x_22 = l_Lake_buildO___lam__2___closed__1;
x_23 = lean_array_to_list(x_1);
x_24 = l_List_toString___at___00Lake_buildLeanO_spec__0(x_23);
lean_dec(x_23);
x_25 = lean_string_append(x_22, x_24);
lean_dec_ref(x_24);
x_26 = lean_string_append(x_21, x_25);
lean_dec_ref(x_25);
x_27 = l_Lake_platformTrace___closed__4;
x_28 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_20);
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
lean_closure_set(x_38, 1, x_19);
lean_closure_set(x_38, 2, x_4);
lean_closure_set(x_38, 3, x_8);
x_39 = l_Lake_BuildTrace_mix(x_36, x_34);
lean_ctor_set(x_33, 1, x_39);
x_40 = 1;
x_41 = 0;
x_42 = l_Lake_sharedLibExt;
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
lean_closure_set(x_62, 1, x_19);
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
x_67 = l_Lake_sharedLibExt;
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
x_87 = lean_unsigned_to_nat(0u);
x_88 = l_Lake_platformTrace___closed__2;
x_89 = l_Lake_buildO___lam__2___closed__0;
x_90 = l_Lake_buildO___lam__2___closed__1;
x_91 = lean_array_to_list(x_1);
x_92 = l_List_toString___at___00Lake_buildLeanO_spec__0(x_91);
lean_dec(x_91);
x_93 = lean_string_append(x_90, x_92);
lean_dec_ref(x_92);
x_94 = lean_string_append(x_89, x_93);
lean_dec_ref(x_93);
x_95 = l_Lake_platformTrace___closed__4;
x_96 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_88);
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
lean_closure_set(x_110, 1, x_87);
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
x_115 = l_Lake_sharedLibExt;
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
static lean_object* _init_l_Lake_buildSharedLib___lam__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("linkLibs", 8, 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_20 = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__0___boxed), 13, 5);
lean_closure_set(x_20, 0, x_11);
lean_closure_set(x_20, 1, x_1);
lean_closure_set(x_20, 2, x_2);
lean_closure_set(x_20, 3, x_3);
lean_closure_set(x_20, 4, x_4);
x_21 = lean_box(x_6);
x_22 = lean_box(x_8);
x_23 = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__2___boxed), 15, 7);
lean_closure_set(x_23, 0, x_2);
lean_closure_set(x_23, 1, x_5);
lean_closure_set(x_23, 2, x_21);
lean_closure_set(x_23, 3, x_20);
lean_closure_set(x_23, 4, x_3);
lean_closure_set(x_23, 5, x_7);
lean_closure_set(x_23, 6, x_22);
x_24 = l_Lake_buildSharedLib___lam__3___closed__0;
x_25 = l_Lake_Job_collectArray___redArg(x_9, x_24);
x_26 = lean_unsigned_to_nat(0u);
x_27 = 0;
lean_inc_ref(x_19);
x_28 = l_Lake_Job_mapM___redArg(x_10, x_25, x_23, x_26, x_27, x_12, x_13, x_14, x_15, x_16, x_19);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_17);
return x_29;
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
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_unbox(x_6);
x_20 = lean_unbox(x_8);
x_21 = l_Lake_buildSharedLib___lam__3(x_1, x_2, x_3, x_4, x_5, x_19, x_7, x_20, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec_ref(x_9);
return x_21;
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_18 = l_Lake_instDataKindDynlib;
x_19 = lean_box(x_10);
x_20 = lean_box(x_9);
x_21 = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__3___boxed), 18, 10);
lean_closure_set(x_21, 0, x_5);
lean_closure_set(x_21, 1, x_6);
lean_closure_set(x_21, 2, x_2);
lean_closure_set(x_21, 3, x_7);
lean_closure_set(x_21, 4, x_8);
lean_closure_set(x_21, 5, x_19);
lean_closure_set(x_21, 6, x_1);
lean_closure_set(x_21, 7, x_20);
lean_closure_set(x_21, 8, x_4);
lean_closure_set(x_21, 9, x_18);
x_22 = l_Lake_buildSharedLib___closed__0;
x_23 = l_Lake_Job_collectArray___redArg(x_3, x_22);
x_24 = lean_unsigned_to_nat(0u);
x_25 = 1;
x_26 = l_Lake_Job_bindM___redArg(x_18, x_23, x_21, x_24, x_25, x_11, x_12, x_13, x_14, x_15, x_16);
return x_26;
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
x_1 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1;
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
x_66 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1;
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
x_57 = l_Lake_Hash_nil;
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_array_get_size(x_3);
x_60 = lean_nat_dec_lt(x_58, x_59);
if (x_60 == 0)
{
x_25 = x_57;
goto block_56;
}
else
{
uint8_t x_61; 
x_61 = lean_nat_dec_le(x_59, x_59);
if (x_61 == 0)
{
if (x_60 == 0)
{
x_25 = x_57;
goto block_56;
}
else
{
size_t x_62; size_t x_63; uint64_t x_64; 
x_62 = 0;
x_63 = lean_usize_of_nat(x_59);
x_64 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(x_3, x_62, x_63, x_57);
x_25 = x_64;
goto block_56;
}
}
else
{
size_t x_65; size_t x_66; uint64_t x_67; 
x_65 = 0;
x_66 = lean_usize_of_nat(x_59);
x_67 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(x_3, x_65, x_66, x_57);
x_25 = x_67;
goto block_56;
}
}
block_56:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_26 = l_Lake_buildO___lam__2___closed__0;
x_27 = l_Lake_buildO___lam__2___closed__1;
x_28 = lean_array_to_list(x_3);
x_29 = l_List_toString___at___00Lake_buildLeanO_spec__0(x_28);
lean_dec(x_28);
x_30 = lean_string_append(x_27, x_29);
lean_dec_ref(x_29);
x_31 = lean_string_append(x_26, x_30);
lean_dec_ref(x_30);
x_32 = l_Lake_platformTrace___closed__2;
x_33 = l_Lake_platformTrace___closed__4;
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
x_40 = l_Lake_sharedLibExt;
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
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_15, 1);
x_18 = lean_box(x_4);
x_19 = lean_box(x_6);
x_20 = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__1___boxed), 15, 7);
lean_closure_set(x_20, 0, x_9);
lean_closure_set(x_20, 1, x_1);
lean_closure_set(x_20, 2, x_2);
lean_closure_set(x_20, 3, x_3);
lean_closure_set(x_20, 4, x_18);
lean_closure_set(x_20, 5, x_5);
lean_closure_set(x_20, 6, x_19);
x_21 = l_Lake_buildSharedLib___lam__3___closed__0;
x_22 = l_Lake_Job_collectArray___redArg(x_7, x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = 0;
lean_inc_ref(x_17);
x_25 = l_Lake_Job_mapM___redArg(x_8, x_22, x_20, x_23, x_24, x_10, x_11, x_12, x_13, x_14, x_17);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_15);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_4);
x_18 = lean_unbox(x_6);
x_19 = l_Lake_buildLeanSharedLib___lam__2(x_1, x_2, x_3, x_17, x_5, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_7);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_16 = l_Lake_instDataKindDynlib;
x_17 = lean_box(x_8);
x_18 = lean_box(x_7);
x_19 = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lam__2___boxed), 16, 8);
lean_closure_set(x_19, 0, x_5);
lean_closure_set(x_19, 1, x_6);
lean_closure_set(x_19, 2, x_2);
lean_closure_set(x_19, 3, x_17);
lean_closure_set(x_19, 4, x_1);
lean_closure_set(x_19, 5, x_18);
lean_closure_set(x_19, 6, x_4);
lean_closure_set(x_19, 7, x_16);
x_20 = l_Lake_buildSharedLib___closed__0;
x_21 = l_Lake_Job_collectArray___redArg(x_3, x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = 1;
x_24 = l_Lake_Job_bindM___redArg(x_16, x_21, x_19, x_22, x_23, x_9, x_10, x_11, x_12, x_13, x_14);
return x_24;
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
x_53 = l_Lake_Hash_nil;
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_array_get_size(x_3);
x_56 = lean_nat_dec_lt(x_54, x_55);
if (x_56 == 0)
{
x_23 = x_53;
goto block_52;
}
else
{
uint8_t x_57; 
x_57 = lean_nat_dec_le(x_55, x_55);
if (x_57 == 0)
{
if (x_56 == 0)
{
x_23 = x_53;
goto block_52;
}
else
{
size_t x_58; size_t x_59; uint64_t x_60; 
x_58 = 0;
x_59 = lean_usize_of_nat(x_55);
x_60 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(x_3, x_58, x_59, x_53);
x_23 = x_60;
goto block_52;
}
}
else
{
size_t x_61; size_t x_62; uint64_t x_63; 
x_61 = 0;
x_62 = lean_usize_of_nat(x_55);
x_63 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanO_spec__1(x_3, x_61, x_62, x_53);
x_23 = x_63;
goto block_52;
}
}
block_52:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_24 = l_Lake_buildO___lam__2___closed__0;
x_25 = l_Lake_buildO___lam__2___closed__1;
x_26 = lean_array_to_list(x_3);
x_27 = l_List_toString___at___00Lake_buildLeanO_spec__0(x_26);
lean_dec(x_26);
x_28 = lean_string_append(x_25, x_27);
lean_dec_ref(x_27);
x_29 = lean_string_append(x_24, x_28);
lean_dec_ref(x_28);
x_30 = l_Lake_platformTrace___closed__2;
x_31 = l_Lake_platformTrace___closed__4;
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
x_38 = l_System_FilePath_exeExtension;
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
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
x_15 = l_Lake_buildLeanExe___lam__1(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_13, 1);
x_16 = lean_box(x_3);
x_17 = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__1___boxed), 13, 5);
lean_closure_set(x_17, 0, x_7);
lean_closure_set(x_17, 1, x_1);
lean_closure_set(x_17, 2, x_2);
lean_closure_set(x_17, 3, x_16);
lean_closure_set(x_17, 4, x_4);
x_18 = l_Lake_buildSharedLib___lam__3___closed__0;
x_19 = l_Lake_Job_collectArray___redArg(x_5, x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = 0;
lean_inc_ref(x_15);
x_22 = l_Lake_Job_mapM___redArg(x_6, x_19, x_17, x_20, x_21, x_8, x_9, x_10, x_11, x_12, x_15);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_13);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_3);
x_16 = l_Lake_buildLeanExe___lam__2(x_1, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_14 = l_Lake_instDataKindFilePath;
x_15 = lean_box(x_6);
x_16 = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lam__2___boxed), 14, 6);
lean_closure_set(x_16, 0, x_4);
lean_closure_set(x_16, 1, x_5);
lean_closure_set(x_16, 2, x_15);
lean_closure_set(x_16, 3, x_1);
lean_closure_set(x_16, 4, x_3);
lean_closure_set(x_16, 5, x_14);
x_17 = l_Lake_buildSharedLib___closed__0;
x_18 = l_Lake_Job_collectArray___redArg(x_2, x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = 1;
x_21 = l_Lake_Job_bindM___redArg(x_14, x_18, x_16, x_19, x_20, x_7, x_8, x_9, x_10, x_11, x_12);
return x_21;
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
l_Lake_platformTrace___closed__1 = _init_l_Lake_platformTrace___closed__1();
l_Lake_platformTrace___closed__2 = _init_l_Lake_platformTrace___closed__2();
lean_mark_persistent(l_Lake_platformTrace___closed__2);
l_Lake_platformTrace___closed__3 = _init_l_Lake_platformTrace___closed__3();
lean_mark_persistent(l_Lake_platformTrace___closed__3);
l_Lake_platformTrace___closed__4 = _init_l_Lake_platformTrace___closed__4();
lean_mark_persistent(l_Lake_platformTrace___closed__4);
l_Lake_platformTrace___closed__5 = _init_l_Lake_platformTrace___closed__5();
lean_mark_persistent(l_Lake_platformTrace___closed__5);
l_Lake_platformTrace = _init_l_Lake_platformTrace();
lean_mark_persistent(l_Lake_platformTrace);
l_Lake_addPureTrace___redArg___closed__0 = _init_l_Lake_addPureTrace___redArg___closed__0();
lean_mark_persistent(l_Lake_addPureTrace___redArg___closed__0);
l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0 = _init_l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion___closed__0);
l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion = _init_l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_BuildMetadata_schemaVersion);
l_Prod_toJson___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__0___closed__0 = _init_l_Prod_toJson___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__0___closed__0();
lean_mark_persistent(l_Prod_toJson___at___00Array_toJson___at___00Lake_BuildMetadata_toJson_spec__0_spec__0___closed__0);
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
l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___closed__0 = _init_l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___closed__0();
lean_mark_persistent(l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__0___closed__0);
l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3___closed__0 = _init_l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3___closed__0();
lean_mark_persistent(l_Option_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2_spec__3___closed__0);
l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2___closed__0 = _init_l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2___closed__0();
lean_mark_persistent(l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__2___closed__0);
l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__0 = _init_l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__0();
lean_mark_persistent(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__0);
l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1 = _init_l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1();
lean_mark_persistent(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1_spec__1___closed__1);
l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1___closed__0 = _init_l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1___closed__0();
lean_mark_persistent(l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__1___closed__0);
l_Prod_fromJson_x3f___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__0 = _init_l_Prod_fromJson_x3f___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__0();
lean_mark_persistent(l_Prod_fromJson_x3f___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3_spec__5_spec__7___closed__0);
l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3___closed__0 = _init_l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3___closed__0();
lean_mark_persistent(l_Option_fromJson_x3f___at___00Lake_BuildMetadata_fromJsonObject_x3f_spec__3___closed__0);
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
l_Lake_instFromJsonBuildMetadata___closed__0 = _init_l_Lake_instFromJsonBuildMetadata___closed__0();
lean_mark_persistent(l_Lake_instFromJsonBuildMetadata___closed__0);
l_Lake_instFromJsonBuildMetadata = _init_l_Lake_instFromJsonBuildMetadata();
lean_mark_persistent(l_Lake_instFromJsonBuildMetadata);
l_Lake_readTraceFile___closed__0 = _init_l_Lake_readTraceFile___closed__0();
lean_mark_persistent(l_Lake_readTraceFile___closed__0);
l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0 = _init_l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___redArg___closed__0);
l_Lake_instToOutputJsonPUnit___closed__0 = _init_l_Lake_instToOutputJsonPUnit___closed__0();
lean_mark_persistent(l_Lake_instToOutputJsonPUnit___closed__0);
l_Lake_instToOutputJsonPUnit = _init_l_Lake_instToOutputJsonPUnit();
lean_mark_persistent(l_Lake_instToOutputJsonPUnit);
l_Lake_instToOutputJsonArtifact___lam__0___closed__0 = _init_l_Lake_instToOutputJsonArtifact___lam__0___closed__0();
lean_mark_persistent(l_Lake_instToOutputJsonArtifact___lam__0___closed__0);
l_Lake_instToOutputJsonArtifact___closed__0 = _init_l_Lake_instToOutputJsonArtifact___closed__0();
lean_mark_persistent(l_Lake_instToOutputJsonArtifact___closed__0);
l_Lake_instToOutputJsonArtifact = _init_l_Lake_instToOutputJsonArtifact();
lean_mark_persistent(l_Lake_instToOutputJsonArtifact);
l_Lake_buildAction___redArg___closed__0 = _init_l_Lake_buildAction___redArg___closed__0();
lean_mark_persistent(l_Lake_buildAction___redArg___closed__0);
l_Lake_buildAction___redArg___closed__1 = _init_l_Lake_buildAction___redArg___closed__1();
lean_mark_persistent(l_Lake_buildAction___redArg___closed__1);
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
l_Lake_cacheArtifact___redArg___closed__0 = _init_l_Lake_cacheArtifact___redArg___closed__0();
lean_mark_persistent(l_Lake_cacheArtifact___redArg___closed__0);
l_Lake_getArtifacts_x3f___redArg___closed__0 = _init_l_Lake_getArtifacts_x3f___redArg___closed__0();
lean_mark_persistent(l_Lake_getArtifacts_x3f___redArg___closed__0);
l_Lake_getArtifacts_x3f___redArg___closed__1 = _init_l_Lake_getArtifacts_x3f___redArg___closed__1();
lean_mark_persistent(l_Lake_getArtifacts_x3f___redArg___closed__1);
l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__0 = _init_l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__0();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__0);
l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__1 = _init_l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__1();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_resolveArtifactOutput_x3f___redArg___closed__1);
l_Lake_buildArtifactUnlessUpToDate___lam__0___closed__0 = _init_l_Lake_buildArtifactUnlessUpToDate___lam__0___closed__0();
lean_mark_persistent(l_Lake_buildArtifactUnlessUpToDate___lam__0___closed__0);
l_Lake_buildFileAfterDep___redArg___lam__0___closed__0 = _init_l_Lake_buildFileAfterDep___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lake_buildFileAfterDep___redArg___lam__0___closed__0);
l_Lake_inputBinFile___redArg___closed__0 = _init_l_Lake_inputBinFile___redArg___closed__0();
lean_mark_persistent(l_Lake_inputBinFile___redArg___closed__0);
l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg___closed__0 = _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_inputDir_spec__1___redArg___closed__0);
l_Lake_inputDir___lam__1___closed__0 = _init_l_Lake_inputDir___lam__1___closed__0();
lean_mark_persistent(l_Lake_inputDir___lam__1___closed__0);
l_Lake_inputDir___closed__0 = _init_l_Lake_inputDir___closed__0();
lean_mark_persistent(l_Lake_inputDir___closed__0);
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
l_Lake_buildO___closed__1 = _init_l_Lake_buildO___closed__1();
lean_mark_persistent(l_Lake_buildO___closed__1);
l_Lake_buildLeanO___lam__0___closed__0 = _init_l_Lake_buildLeanO___lam__0___closed__0();
lean_mark_persistent(l_Lake_buildLeanO___lam__0___closed__0);
l_Lake_buildLeanO___lam__0___closed__1 = _init_l_Lake_buildLeanO___lam__0___closed__1();
lean_mark_persistent(l_Lake_buildLeanO___lam__0___closed__1);
l_Lake_buildLeanO___lam__0___closed__2 = _init_l_Lake_buildLeanO___lam__0___closed__2();
lean_mark_persistent(l_Lake_buildLeanO___lam__0___closed__2);
l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___closed__0 = _init_l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___closed__0();
lean_mark_persistent(l_List_foldl___at___00List_toString___at___00Lake_buildLeanO_spec__0_spec__0___closed__0);
l_List_toString___at___00Lake_buildLeanO_spec__0___closed__0 = _init_l_List_toString___at___00Lake_buildLeanO_spec__0___closed__0();
lean_mark_persistent(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__0);
l_List_toString___at___00Lake_buildLeanO_spec__0___closed__1 = _init_l_List_toString___at___00Lake_buildLeanO_spec__0___closed__1();
lean_mark_persistent(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__1);
l_List_toString___at___00Lake_buildLeanO_spec__0___closed__2 = _init_l_List_toString___at___00Lake_buildLeanO_spec__0___closed__2();
lean_mark_persistent(l_List_toString___at___00Lake_buildLeanO_spec__0___closed__2);
l_Lake_buildStaticLib___lam__1___closed__0 = _init_l_Lake_buildStaticLib___lam__1___closed__0();
lean_mark_persistent(l_Lake_buildStaticLib___lam__1___closed__0);
l_Lake_buildStaticLib___closed__0 = _init_l_Lake_buildStaticLib___closed__0();
lean_mark_persistent(l_Lake_buildStaticLib___closed__0);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1);
l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0___closed__0 = _init_l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0___closed__0();
lean_mark_persistent(l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0_spec__0___closed__0);
l_Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0___closed__0 = _init_l_Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0___closed__0();
lean_mark_persistent(l_Lake_formatCycle___at___00__private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0___closed__0);
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

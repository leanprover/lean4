// Lean compiler output
// Module: Lake.Build.Common
// Imports: Lean.Data.Json Lake.Build.Job.Monad Lake.Config.Monad Lake.Util.IO Lake.Util.JsonObject Lake.Build.Target.Fetch Lake.Build.Actions
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
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_BuildMetadata_parse_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFromJsonFileOutputHash(lean_object*);
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(lean_object*, lean_object*);
lean_object* l_Lake_compileO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildO___closed__0;
static lean_object* l_Lake_buildO___lam__2___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildSharedLib___lam__3___closed__0;
LEAN_EXPORT lean_object* l_Lake_writeFileHash(lean_object*, uint64_t, lean_object*);
static lean_object* l_Lake_instFromJsonBuildMetadata___closed__0;
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ctorIdx___boxed(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldl___at___List_toString___at___Lake_buildLeanO_spec__0_spec__0___closed__0;
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__8;
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildFileAfterDep___redArg___lam__0___closed__0;
static lean_object* l_List_mapTR_loop___at___Lake_formatCycle___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1_spec__1___closed__0;
LEAN_EXPORT lean_object* l_Lake_fetchFileHash(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatCycle___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_addLeanTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_remove_file(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at___Lake_buildLeanO_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___List_toString___at___Lake_buildLeanO_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5___closed__0;
lean_object* l_Lake_Job_mapM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
static lean_object* l_Lake_buildStaticLib___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_writeFile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stdout(lean_object*, lean_object*);
static lean_object* l_Lake_toJsonBuildMetadata___closed__2____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_;
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__10;
lean_object* l_Lake_compileSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_byte_array_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__7_spec__7(lean_object*);
static lean_object* l_Lake_buildLeanO___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_serializeInputs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_toJson___at___Array_toJson___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__0_spec__0(lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Prod_fromJson_x3f___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__7_spec__7_spec__7___closed__0;
lean_object* l_Lake_computeTextFileHash(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayOrFetch_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__14;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayOrFetch_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetch(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__3;
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_metadata(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchLocalArtifact___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPureTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l_Lake_platformTrace___closed__1;
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_System_FilePath_exeExtension;
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_BuildMetadata_parse_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_buildLeanO_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l_Lake_platformTrace___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lake_EStateT_instPure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayOrFetch_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__0;
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__13;
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0___boxed(lean_object*);
lean_object* l_IO_FS_DirEntry_path(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__7_spec__7_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2;
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__6;
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_IO_FS_ordSystemTime____x40_Init_System_IO_1242411632____hygCtx___hyg_51_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_inputDir_spec__3(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_toString___at___Lake_buildLeanO_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_CacheMap_insertCore(uint64_t, lean_object*, lean_object*);
lean_object* l_Lake_Hash_ofString_x3f(lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonPUnit__lake___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EquipT_instMonad___redArg(lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
static lean_object* l_Lake_platformTrace___closed__7;
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofStub(uint64_t);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__2___closed__0;
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instToStringString___lam__0___boxed(lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_readTraceFile_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Dynlib_dir_x3f(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lake_BuildTrace_mix(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
static lean_object* l_Prod_toJson___at___Array_toJson___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildArtifactUnlessUpToDate___closed__0;
lean_object* l_Lake_compileExe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__7_spec__7_spec__7(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_crlfToLf(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___at___Array_appendList_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_IO_FS_writeBinFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveArtifactsUsing_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
extern lean_object* l_Lake_sharedLibExt;
LEAN_EXPORT lean_object* l_Lake_ResolveArtifacts_ctorIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofHash(uint64_t);
static lean_object* l_Lake_readTraceFile___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_platformTrace;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__2;
uint8_t l_Option_beqOption___redArg____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_writeFileHash___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_inputBinFile___redArg___closed__1;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lake_inputDir_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now(lean_object*);
lean_object* lean_task_pure(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_toJson___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addLeanTrace___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__0;
lean_object* l_UInt64_fromJson_x3f(lean_object*);
lean_object* l_Lake_createParentDirs(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instFunctor___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__2_spec__2_spec__2(size_t, size_t, lean_object*);
lean_object* l_Lake_fromJsonLogEntry____x40_Lake_Util_Log_2045950852____hygCtx___hyg_41_(lean_object*);
static lean_object* l_Lake_toJsonBuildMetadata___closed__0____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_;
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceJobM;
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___Lake_inputTextFile_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__11;
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__8;
extern lean_object* l_ByteArray_empty;
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_parse(lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchLocalArtifact___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildAction___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__12;
LEAN_EXPORT lean_object* l_Lake_readTraceFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__3___boxed(lean_object**);
static lean_object* l_Lake_buildSharedLib___lam__2___closed__0;
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__1;
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFromJsonBuildMetadata;
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instAlternativeOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0(lean_object*);
static lean_object* l_Lake_platformTrace___closed__0;
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Lake_JobM_runFetchM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_collectArray___redArg(lean_object*, lean_object*);
static uint64_t l_Lake_platformTrace___closed__3;
LEAN_EXPORT lean_object* l_Lake_buildO___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instResolveArtifactsFileOutputHashArtifactOfMonadLakeEnvOfMonadLiftTBaseIOOfMonad___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at_____private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__0;
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildAction___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_resolveArtifactsUsing_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_instDataKindFilePath;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_inputBinFile___redArg___lam__1___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lake_buildSharedLib___closed__0;
lean_object* l_Lake_Cache_getArtifact_x3f(lean_object*, uint64_t, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lake_EStateT_instPure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofHash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildO___lam__2___closed__2;
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instAlternativeELogTOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_JobState_merge(lean_object*, lean_object*);
lean_object* l_Lake_CacheMap_get_x3f(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ResolveArtifacts_ctorIdx(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__7;
static lean_object* l_Lake_toJsonBuildMetadata___closed__1____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_;
static lean_object* l_Lake_inputBinFile___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__2_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_serializeInputs(lean_object*);
lean_object* l_Lake_copyFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayOrFetch_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_toString___at___Lake_buildLeanO_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheFileHash(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofFetch(uint64_t, lean_object*);
static lean_object* l_panic___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__3___closed__0;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArtifactTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveArtifactsUsing_x3f___at___Lake_buildArtifactUnlessUpToDate_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__17;
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildLeanExe___lam__1___closed__0;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_toJson___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_toJson___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__6;
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_BuildMetadata_parse_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__2_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_platformTrace___closed__4;
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArtifactTrace(lean_object*, lean_object*, uint64_t, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildTrace_nil(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonFileOutputHash(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instResolveArtifactsFileOutputHashArtifactOfMonadLakeEnvOfMonadLiftTBaseIOOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint64_t);
lean_object* lean_get_set_stderr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EquipT_instFunctor___redArg(lean_object*);
static lean_object* l_Lake_buildLeanSharedLib___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
static lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0;
static lean_object* l_Lake_instToJsonBuildMetadata___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__15;
LEAN_EXPORT lean_object* l_Lake_fetchLocalArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__2;
static lean_object* l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__2_spec__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_serializeInputs___boxed(lean_object*);
lean_object* l_Lake_Cache_getArtifact_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__4(lean_object*);
static lean_object* l_Lake_checkHashUpToDate___redArg___closed__0;
static lean_object* l_Lake_toJsonBuildMetadata___closed__3____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_;
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildLeanO___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_FileOutputHash_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__0(lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_platformTrace___closed__6;
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_readTraceFile___closed__1;
LEAN_EXPORT lean_object* l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder_go(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lake_writeFileHash___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__1;
static lean_object* l_Lake_buildStaticLib___lam__1___closed__0;
static lean_object* l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__7___closed__0;
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofStub___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__0;
static lean_object* l_Lake_resolveArtifactsUsing_x3f___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonFileOutputHash___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPureTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___List_toString___at___Lake_buildLeanO_spec__0_spec__0(lean_object*, lean_object*);
lean_object* l_EStateM_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_toJson___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__4_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__7(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lake_Hash_load_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lake_inputDir_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_FileOutputHash_ctorIdx(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Lake_resolveArtifactsUsing_x3f(lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Option_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5_spec__5___closed__0;
LEAN_EXPORT lean_object* l_Lake_inputFile(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at_____private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg___lam__0(lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__9;
LEAN_EXPORT lean_object* l_Lake_instResolveArtifactsFileOutputHashArtifactOfMonadLakeEnvOfMonadLiftTBaseIOOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lake_inputDir_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lake_EquipT_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern uint64_t l_Lake_Hash_nil;
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofFetch___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_buildLeanO_spec__2(lean_object*, size_t, size_t, uint64_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_instToJsonPUnit__lake;
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildFileUnlessUpToDate_x27___closed__0;
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at_____private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_instDataKindDynlib;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofBuild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at___Lake_inputBinFile_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lake_inputDir_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Artifact_trace(lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instResolveArtifactsFileOutputHashArtifactOfMonadLakeEnvOfMonadLiftTBaseIOOfMonad___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheArtifact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeTraceFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_serializeInputs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__4;
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lake_formatCycle___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1_spec__1(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__4;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_get_set_stdin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__5;
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_toJsonLogEntry____x40_Lake_Util_Log_2045950852____hygCtx___hyg_31_(lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__18;
lean_object* l_Lake_LeanInstall_ccLinkFlags(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeTraceFile___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lake_Build_Common_0__Lake_mkLinkObjArgs_spec__1___closed__1;
uint8_t l_Lake_JobAction_merge(uint8_t, uint8_t);
LEAN_EXPORT uint64_t l_Lake_buildO___lam__0(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_serializeInputs_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_bignumToJson(lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveArtifactsUsing_x3f___redArg(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonBuildMetadata;
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* lean_io_read_dir(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_go_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_MTime_checkUpToDate___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_BuildMetadata_parse_spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__20;
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lake_compileStaticLib(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_resolveArtifactsUsing_x3f___at___Lake_buildArtifactUnlessUpToDate_spec__0(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_toJsonBuildMetadata___closed__5____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_;
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildLeanO___lam__0___closed__2;
lean_object* l_Lake_EStateT_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeTraceFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFromJsonFileOutputHash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeFetchTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_computeBinFileHash(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lake_buildO___lam__2___closed__1;
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_inputBinFile___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_inputDir_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__5;
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instResolveArtifactsFileOutputHashArtifactOfMonadLakeEnvOfMonadLiftTBaseIOOfMonad___redArg___lam__0(uint64_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__1___closed__0;
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_writeFile(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__16;
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Cache_artifactPath(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_resolveArtifactsUsing_x3f___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__2___redArg___lam__0(lean_object*, lean_object*);
static lean_object* l_Lake_instMonadWorkspaceJobM___closed__19;
LEAN_EXPORT lean_object* l_Lake_instFromJsonFileOutputHash___lam__0(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_addPureTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__7_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
LEAN_EXPORT lean_object* l_Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_(lean_object*);
static lean_object* l_Lake_formatCycle___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1___closed__0;
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lake_instDecidableEqHash___boxed(lean_object*, lean_object*);
lean_object* l_IO_FS_readBinFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchLocalArtifact(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildO___lam__2___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_System_Platform_target;
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeFetchTrace(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonFileOutputHash___lam__0(uint64_t);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonFileOutputHash___boxed(lean_object*);
lean_object* l_IO_setAccessRights(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lake_resolveArtifactsUsing_x3f___redArg___closed__1;
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___boxed(lean_object**);
static lean_object* l_Lake_inputDir___lam__2___closed__0;
lean_object* l_Lake_instMonadLiftLakeMBuildTOfPure___redArg(lean_object*);
static lean_object* l_List_toString___at___Lake_buildLeanO_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_platformTrace___closed__5;
static lean_object* l_Lake_toJsonBuildMetadata___closed__4____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_;
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instResolveArtifactsFileOutputHashArtifactOfMonadLakeEnvOfMonadLiftTBaseIOOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_clearFileHash(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheFileHash___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputFile___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_filterMapM___at___Lake_inputDir_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at___Lake_buildLeanO_spec__0___boxed(lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__7;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_serializeInputs_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJson_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at_____private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__2_spec__2___closed__0;
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
x_58 = lean_alloc_closure((void*)(l_Lake_JobM_runFetchM), 9, 2);
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
x_80 = lean_alloc_closure((void*)(l_Lake_JobM_runFetchM), 9, 2);
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
x_136 = lean_alloc_closure((void*)(l_Lake_JobM_runFetchM), 9, 2);
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
x_195 = lean_alloc_closure((void*)(l_Lake_JobM_runFetchM), 9, 2);
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
x_1 = lean_alloc_closure((void*)(l_Lake_instToJsonPUnit__lake___lam__0), 1, 0);
return x_1;
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
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
lean_dec(x_1);
x_14 = l_Lake_platformTrace;
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
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_2);
return x_19;
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
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
x_17 = lean_ctor_get(x_6, 1);
x_18 = lean_ctor_get(x_6, 2);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_15);
lean_dec(x_6);
x_19 = l_Lake_platformTrace;
x_20 = lean_box(0);
x_21 = l_Lake_BuildTrace_mix(x_17, x_19);
x_22 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_18);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_16);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_7);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lake_addPlatformTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_addPlatformTrace(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
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
lean_inc_ref(x_6);
lean_dec_ref(x_1);
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
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_11);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_15);
lean_dec_ref(x_1);
x_16 = lean_box(0);
x_17 = l_Lake_BuildTrace_mix(x_13, x_15);
x_18 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_14);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_12);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
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
lean_inc_ref(x_10);
lean_dec_ref(x_5);
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
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
x_17 = lean_ctor_get(x_6, 1);
x_18 = lean_ctor_get(x_6, 2);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_15);
lean_dec(x_6);
x_19 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_19);
lean_dec_ref(x_5);
x_20 = lean_box(0);
x_21 = l_Lake_BuildTrace_mix(x_17, x_19);
x_22 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_18);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_16);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_7);
return x_24;
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
LEAN_EXPORT lean_object* l_Lake_addPureTrace___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
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
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_6);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint64_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_22 = lean_ctor_get(x_5, 0);
x_23 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 2);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_22);
lean_dec(x_5);
lean_inc(x_3);
x_26 = lean_apply_1(x_2, x_3);
x_27 = l_Lake_addPureTrace___redArg___closed__0;
x_28 = lean_string_append(x_4, x_27);
x_29 = lean_apply_1(x_1, x_3);
x_30 = lean_string_append(x_28, x_29);
lean_dec_ref(x_29);
x_31 = l_Lake_platformTrace___closed__4;
x_32 = l_Lake_platformTrace___closed__6;
x_33 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_32);
x_34 = lean_unbox_uint64(x_26);
lean_dec(x_26);
lean_ctor_set_uint64(x_33, sizeof(void*)*3, x_34);
x_35 = lean_box(0);
x_36 = l_Lake_BuildTrace_mix(x_24, x_33);
x_37 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_37, 0, x_22);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_25);
lean_ctor_set_uint8(x_37, sizeof(void*)*3, x_23);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_6);
return x_39;
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
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
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_12);
return x_27;
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint64_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_28 = lean_ctor_get(x_11, 0);
x_29 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_30 = lean_ctor_get(x_11, 1);
x_31 = lean_ctor_get(x_11, 2);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_28);
lean_dec(x_11);
lean_inc(x_4);
x_32 = lean_apply_1(x_3, x_4);
x_33 = l_Lake_addPureTrace___redArg___closed__0;
x_34 = lean_string_append(x_5, x_33);
x_35 = lean_apply_1(x_2, x_4);
x_36 = lean_string_append(x_34, x_35);
lean_dec_ref(x_35);
x_37 = l_Lake_platformTrace___closed__4;
x_38 = l_Lake_platformTrace___closed__6;
x_39 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_unbox_uint64(x_32);
lean_dec(x_32);
lean_ctor_set_uint64(x_39, sizeof(void*)*3, x_40);
x_41 = lean_box(0);
x_42 = l_Lake_BuildTrace_mix(x_30, x_39);
x_43 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_43, 0, x_28);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_31);
lean_ctor_set_uint8(x_43, sizeof(void*)*3, x_29);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_12);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Lake_addPureTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_addPureTrace(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
static lean_object* _init_l_Prod_toJson___at___Array_toJson___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Prod_toJson___at___Array_toJson___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__0_spec__0(lean_object* x_1) {
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
x_5 = l_Prod_toJson___at___Array_toJson___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__0_spec__0___closed__0;
x_6 = lean_array_push(x_5, x_4);
x_7 = lean_array_push(x_6, x_3);
x_8 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_toJson___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__0_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = l_Prod_toJson___at___Array_toJson___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__0_spec__0(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__0(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_toJson___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__0_spec__1(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_toJson___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__4_spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = l_Lake_toJsonLogEntry____x40_Lake_Util_Log_2045950852____hygCtx___hyg_31_(x_5);
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
LEAN_EXPORT lean_object* l_Array_toJson___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__4(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_toJson___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__4_spec__4(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_array_to_list(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = l_List_foldl___at___Array_appendList_spec__0___redArg(x_2, x_4);
x_1 = x_5;
x_2 = x_6;
goto _start;
}
}
}
static lean_object* _init_l_Lake_toJsonBuildMetadata___closed__0____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("depHash", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_toJsonBuildMetadata___closed__1____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inputs", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_toJsonBuildMetadata___closed__2____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("outputs", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_toJsonBuildMetadata___closed__3____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("log", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_toJsonBuildMetadata___closed__4____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("synthetic", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_toJsonBuildMetadata___closed__5____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_2 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_5);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec_ref(x_1);
x_7 = l_Lake_toJsonBuildMetadata___closed__0____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_;
x_8 = lean_uint64_to_nat(x_2);
x_9 = l_Lean_bignumToJson(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lake_toJsonBuildMetadata___closed__1____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_;
x_14 = l_Array_toJson___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__0(x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
x_17 = l_Lake_toJsonBuildMetadata___closed__2____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_;
x_18 = l_Lean_Json_opt___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__3(x_17, x_4);
lean_dec(x_4);
x_19 = l_Lake_toJsonBuildMetadata___closed__3____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_;
x_20 = l_Array_toJson___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__4(x_5);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_11);
x_23 = l_Lake_toJsonBuildMetadata___closed__4____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_;
x_24 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_24, 0, x_6);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_11);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_11);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_18);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_16);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_12);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lake_toJsonBuildMetadata___closed__5____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_;
x_33 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__6(x_31, x_32);
x_34 = l_Lean_Json_mkObj(x_33);
return x_34;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_toJson___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_toJson___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__0_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_opt___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__3(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_toJson___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_toJson___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__4_spec__4(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lake_instToJsonBuildMetadata___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_), 1, 0);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_ctor_get(x_1, 4);
x_7 = lean_string_dec_lt(x_2, x_3);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_string_dec_eq(x_2, x_3);
if (x_8 == 0)
{
x_1 = x_6;
goto _start;
}
else
{
lean_object* x_10; 
lean_inc(x_4);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_4);
return x_10;
}
}
else
{
x_1 = x_5;
goto _start;
}
}
else
{
lean_object* x_12; 
x_12 = lean_box(0);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0___redArg(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__1___closed__0;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__2_spec__2_spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_7 = l_Lake_fromJsonLogEntry____x40_Lake_Util_Log_2045950852____hygCtx___hyg_41_(x_6);
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
static lean_object* _init_l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__2_spec__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__2_spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__2_spec__2(lean_object* x_1) {
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
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__2_spec__2_spec__2(x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__2_spec__2___closed__0;
x_7 = lean_unsigned_to_nat(80u);
x_8 = l_Lean_Json_pretty(x_1, x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec_ref(x_8);
x_10 = l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__2_spec__2___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
static lean_object* _init_l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__2___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__2___closed__0;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__2_spec__2(x_1);
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
static lean_object* _init_l_Option_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5_spec__5___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5_spec__5(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5_spec__5___closed__0;
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
lean_object* x_3; uint8_t x_4; 
x_3 = l_Option_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5_spec__5(x_1);
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
static lean_object* _init_l_Prod_fromJson_x3f___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__7_spec__7_spec__7___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected pair, got '", 20, 20);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__7_spec__7_spec__7(lean_object* x_1) {
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
x_3 = l_Prod_fromJson_x3f___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__7_spec__7_spec__7___closed__0;
x_4 = lean_unsigned_to_nat(80u);
x_5 = l_Lean_Json_pretty(x_2, x_4);
x_6 = lean_string_append(x_3, x_5);
lean_dec_ref(x_5);
x_7 = l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__2_spec__2___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__7_spec__7_spec__8(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_7 = l_Prod_fromJson_x3f___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__7_spec__7_spec__7(x_6);
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
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__7_spec__7(lean_object* x_1) {
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
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__7_spec__7_spec__8(x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__2_spec__2___closed__0;
x_7 = lean_unsigned_to_nat(80u);
x_8 = l_Lean_Json_pretty(x_1, x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec_ref(x_8);
x_10 = l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__2_spec__2___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
static lean_object* _init_l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__7___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__7(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__7___closed__0;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__7_spec__7(x_1);
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
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("synthetic: ", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("log: ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("outputs: ", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__8() {
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
lean_dec_ref(x_2);
x_7 = l_Lake_toJsonBuildMetadata___closed__0____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_;
x_8 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0___redArg(x_6, x_7);
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
lean_dec_ref(x_8);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_57; lean_object* x_58; lean_object* x_61; lean_object* x_62; lean_object* x_81; lean_object* x_84; lean_object* x_94; lean_object* x_95; 
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_21 = x_11;
} else {
 lean_dec_ref(x_11);
 x_21 = lean_box(0);
}
x_94 = l_Lake_toJsonBuildMetadata___closed__1____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_;
x_95 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0___redArg(x_6, x_94);
if (lean_obj_tag(x_95) == 0)
{
goto block_93;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_dec_ref(x_95);
x_97 = l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__7(x_96);
if (lean_obj_tag(x_97) == 0)
{
uint8_t x_98; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_6);
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_97, 0);
x_100 = l_Lake_BuildMetadata_fromJson_x3f___closed__8;
x_101 = lean_string_append(x_100, x_99);
lean_dec(x_99);
lean_ctor_set(x_97, 0, x_101);
return x_97;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_97, 0);
lean_inc(x_102);
lean_dec(x_97);
x_103 = l_Lake_BuildMetadata_fromJson_x3f___closed__8;
x_104 = lean_string_append(x_103, x_102);
lean_dec(x_102);
x_105 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_105, 0, x_104);
return x_105;
}
}
else
{
if (lean_obj_tag(x_97) == 0)
{
uint8_t x_106; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_6);
x_106 = !lean_is_exclusive(x_97);
if (x_106 == 0)
{
lean_ctor_set_tag(x_97, 0);
return x_97;
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_97, 0);
lean_inc(x_107);
lean_dec(x_97);
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_107);
return x_108;
}
}
else
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_97, 0);
lean_inc(x_109);
lean_dec_ref(x_97);
if (lean_obj_tag(x_109) == 0)
{
goto block_93;
}
else
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
lean_dec_ref(x_109);
x_84 = x_110;
goto block_91;
}
}
}
}
block_29:
{
lean_object* x_26; uint64_t x_27; lean_object* x_28; 
x_26 = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_23);
x_27 = lean_unbox_uint64(x_20);
lean_dec(x_20);
lean_ctor_set_uint64(x_26, sizeof(void*)*3, x_27);
lean_ctor_set_uint8(x_26, sizeof(void*)*3 + 8, x_25);
if (lean_is_scalar(x_21)) {
 x_28 = lean_alloc_ctor(1, 1, 0);
} else {
 x_28 = x_21;
}
lean_ctor_set(x_28, 0, x_26);
return x_28;
}
block_34:
{
uint8_t x_33; 
x_33 = 0;
x_22 = x_30;
x_23 = x_31;
x_24 = x_32;
x_25 = x_33;
goto block_29;
}
block_56:
{
lean_object* x_38; lean_object* x_39; 
x_38 = l_Lake_toJsonBuildMetadata___closed__4____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_;
x_39 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0___redArg(x_6, x_38);
lean_dec(x_6);
if (lean_obj_tag(x_39) == 0)
{
x_30 = x_35;
x_31 = x_37;
x_32 = x_36;
goto block_34;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__1(x_40);
lean_dec(x_40);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_21);
lean_dec(x_20);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = l_Lake_BuildMetadata_fromJson_x3f___closed__3;
x_45 = lean_string_append(x_44, x_43);
lean_dec(x_43);
lean_ctor_set(x_41, 0, x_45);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_41, 0);
lean_inc(x_46);
lean_dec(x_41);
x_47 = l_Lake_BuildMetadata_fromJson_x3f___closed__3;
x_48 = lean_string_append(x_47, x_46);
lean_dec(x_46);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
else
{
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_50; 
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_35);
lean_dec(x_21);
lean_dec(x_20);
x_50 = !lean_is_exclusive(x_41);
if (x_50 == 0)
{
lean_ctor_set_tag(x_41, 0);
return x_41;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_41, 0);
lean_inc(x_51);
lean_dec(x_41);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
else
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_41, 0);
lean_inc(x_53);
lean_dec_ref(x_41);
if (lean_obj_tag(x_53) == 0)
{
x_30 = x_35;
x_31 = x_37;
x_32 = x_36;
goto block_34;
}
else
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
x_22 = x_35;
x_23 = x_37;
x_24 = x_36;
x_25 = x_55;
goto block_29;
}
}
}
}
}
block_60:
{
lean_object* x_59; 
x_59 = l_Lake_BuildMetadata_fromJson_x3f___closed__4;
x_35 = x_57;
x_36 = x_58;
x_37 = x_59;
goto block_56;
}
block_80:
{
lean_object* x_63; lean_object* x_64; 
x_63 = l_Lake_toJsonBuildMetadata___closed__3____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_;
x_64 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0___redArg(x_6, x_63);
if (lean_obj_tag(x_64) == 0)
{
x_57 = x_61;
x_58 = x_62;
goto block_60;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
x_66 = l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__2(x_65);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_6);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = l_Lake_BuildMetadata_fromJson_x3f___closed__5;
x_70 = lean_string_append(x_69, x_68);
lean_dec(x_68);
lean_ctor_set(x_66, 0, x_70);
return x_66;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_66, 0);
lean_inc(x_71);
lean_dec(x_66);
x_72 = l_Lake_BuildMetadata_fromJson_x3f___closed__5;
x_73 = lean_string_append(x_72, x_71);
lean_dec(x_71);
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
else
{
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_75; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_6);
x_75 = !lean_is_exclusive(x_66);
if (x_75 == 0)
{
lean_ctor_set_tag(x_66, 0);
return x_66;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_66, 0);
lean_inc(x_76);
lean_dec(x_66);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
else
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_66, 0);
lean_inc(x_78);
lean_dec_ref(x_66);
if (lean_obj_tag(x_78) == 0)
{
x_57 = x_61;
x_58 = x_62;
goto block_60;
}
else
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_dec_ref(x_78);
x_35 = x_61;
x_36 = x_62;
x_37 = x_79;
goto block_56;
}
}
}
}
}
block_83:
{
lean_object* x_82; 
x_82 = lean_box(0);
x_61 = x_81;
x_62 = x_82;
goto block_80;
}
block_91:
{
lean_object* x_85; lean_object* x_86; 
x_85 = l_Lake_toJsonBuildMetadata___closed__2____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_;
x_86 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0___redArg(x_6, x_85);
if (lean_obj_tag(x_86) == 0)
{
x_81 = x_84;
goto block_83;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
x_88 = l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5(x_87);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec_ref(x_88);
if (lean_obj_tag(x_89) == 0)
{
x_81 = x_84;
goto block_83;
}
else
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec_ref(x_89);
x_61 = x_84;
x_62 = x_90;
goto block_80;
}
}
}
block_93:
{
lean_object* x_92; 
x_92 = l_Lake_BuildMetadata_fromJson_x3f___closed__7;
x_84 = x_92;
goto block_91;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__2_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__2_spec__2_spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__7_spec__7_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__7_spec__7_spec__8(x_4, x_5, x_3);
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
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofStub(uint64_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = l_Lake_toJsonBuildMetadata___closed__5____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_;
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
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_BuildMetadata_parse_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_BuildMetadata_parse_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_parse(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = l_Substring_takeWhileAux___at___Lake_BuildMetadata_parse_spec__0(x_1, x_3, x_2);
x_5 = l_Substring_takeRightWhileAux___at___Lake_BuildMetadata_parse_spec__1(x_1, x_4, x_3);
x_6 = lean_string_utf8_extract(x_1, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
x_7 = l_Lake_Hash_ofString_x3f(x_6);
lean_dec_ref(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = l_Lean_Json_parse(x_1);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec_ref(x_8);
x_13 = l_Lake_BuildMetadata_fromJson_x3f(x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec_ref(x_1);
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
lean_object* x_15; uint64_t x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_unbox_uint64(x_15);
lean_dec(x_15);
x_17 = l_Lake_BuildMetadata_ofStub(x_16);
lean_ctor_set(x_7, 0, x_17);
return x_7;
}
else
{
lean_object* x_18; uint64_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_7, 0);
lean_inc(x_18);
lean_dec(x_7);
x_19 = lean_unbox_uint64(x_18);
lean_dec(x_18);
x_20 = l_Lake_BuildMetadata_ofStub(x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_BuildMetadata_parse_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeWhileAux___at___Lake_BuildMetadata_parse_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_BuildMetadata_parse_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeRightWhileAux___at___Lake_BuildMetadata_parse_spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofFetch(uint64_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_3 = l_Lake_toJsonBuildMetadata___closed__5____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_;
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
x_19 = l_Array_toJson___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__0(x_18);
x_7 = x_19;
goto block_14;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_15);
x_20 = lean_uint64_to_nat(x_16);
x_21 = l_Lean_bignumToJson(x_20);
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
x_19 = l_Array_toJson___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__0(x_18);
x_7 = x_19;
goto block_14;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_15);
x_20 = lean_uint64_to_nat(x_16);
x_21 = l_Lean_bignumToJson(x_20);
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
x_2 = l_Lake_BuildMetadata_fromJson_x3f___closed__7;
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
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lake_BuildMetadata_parse(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = l_Lake_readTraceFile___closed__0;
x_10 = lean_string_append(x_1, x_9);
x_11 = lean_string_append(x_10, x_8);
lean_dec(x_8);
x_12 = 0;
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_12);
x_14 = lean_array_push(x_2, x_13);
x_15 = lean_box(1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_4, 0, x_16);
return x_4;
}
else
{
uint8_t x_17; 
lean_dec_ref(x_1);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; 
lean_ctor_set_tag(x_7, 2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_2);
lean_ctor_set(x_4, 0, x_18);
return x_4;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
lean_dec(x_7);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_2);
lean_ctor_set(x_4, 0, x_21);
return x_4;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_4, 0);
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_4);
x_24 = l_Lake_BuildMetadata_parse(x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = l_Lake_readTraceFile___closed__0;
x_27 = lean_string_append(x_1, x_26);
x_28 = lean_string_append(x_27, x_25);
lean_dec(x_25);
x_29 = 0;
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_29);
x_31 = lean_array_push(x_2, x_30);
x_32 = lean_box(1);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_23);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec_ref(x_1);
x_35 = lean_ctor_get(x_24, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 x_36 = x_24;
} else {
 lean_dec_ref(x_24);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(2, 1, 0);
} else {
 x_37 = x_36;
 lean_ctor_set_tag(x_37, 2);
}
lean_ctor_set(x_37, 0, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_2);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_23);
return x_39;
}
}
}
else
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_4, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 11)
{
uint8_t x_41; 
lean_dec_ref(x_40);
lean_dec_ref(x_1);
x_41 = !lean_is_exclusive(x_4);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_4, 0);
lean_dec(x_42);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_2);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_44);
return x_4;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_4, 1);
lean_inc(x_45);
lean_dec(x_4);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_2);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_4);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_50 = lean_ctor_get(x_4, 0);
lean_dec(x_50);
x_51 = l_Lake_readTraceFile___closed__1;
x_52 = lean_string_append(x_1, x_51);
x_53 = lean_io_error_to_string(x_40);
x_54 = lean_string_append(x_52, x_53);
lean_dec_ref(x_53);
x_55 = 2;
x_56 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_55);
x_57 = lean_array_push(x_2, x_56);
x_58 = lean_box(1);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_59);
return x_4;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_60 = lean_ctor_get(x_4, 1);
lean_inc(x_60);
lean_dec(x_4);
x_61 = l_Lake_readTraceFile___closed__1;
x_62 = lean_string_append(x_1, x_61);
x_63 = lean_io_error_to_string(x_40);
x_64 = lean_string_append(x_62, x_63);
lean_dec_ref(x_63);
x_65 = 2;
x_66 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set_uint8(x_66, sizeof(void*)*1, x_65);
x_67 = lean_array_push(x_2, x_66);
x_68 = lean_box(1);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_60);
return x_70;
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
lean_inc_ref(x_15);
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
lean_inc_ref(x_22);
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
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_writeFile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_createParentDirs(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = l_Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_(x_2);
x_7 = lean_unsigned_to_nat(80u);
x_8 = l_Lean_Json_pretty(x_6, x_7);
x_9 = l_IO_FS_writeFile(x_1, x_8, x_5);
lean_dec_ref(x_8);
return x_9;
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
x_4 = l_Lake_BuildMetadata_writeFile(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_writeFetchTrace(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lake_BuildMetadata_ofFetch(x_2, x_3);
x_6 = l_Lake_BuildMetadata_writeFile(x_1, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_writeFetchTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_6 = l_Lake_writeFetchTrace(x_1, x_5, x_3, x_4);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_apply_1(x_1, x_4);
x_8 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_3, x_7, x_5);
x_9 = l_Lake_BuildMetadata_writeFile(x_2, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_apply_1(x_2, x_5);
x_9 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_4, x_8, x_6);
x_10 = l_Lake_BuildMetadata_writeFile(x_3, x_9, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_writeBuildTrace___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_writeBuildTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_writeBuildTrace(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_writeTraceFile___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_apply_1(x_1, x_4);
x_8 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_3, x_7, x_5);
x_9 = l_Lake_BuildMetadata_writeFile(x_2, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_writeTraceFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_apply_1(x_2, x_5);
x_9 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_4, x_8, x_6);
x_10 = l_Lake_BuildMetadata_writeFile(x_3, x_9, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_writeTraceFile___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_writeTraceFile___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_writeTraceFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_writeTraceFile(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
static lean_object* _init_l_Lake_checkHashUpToDate___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lake_instDecidableEqHash___boxed), 2, 0);
x_2 = l_instBEqOfDecidableEq___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint64_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_11 = l_Lake_checkHashUpToDate___redArg___closed__0;
x_12 = lean_box_uint64(x_10);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Option_beqOption___redArg____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3_(x_11, x_13, x_5);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
lean_dec_ref(x_1);
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_8);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_9);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lake_MTime_checkUpToDate___redArg(x_2, x_3, x_6, x_9);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_8);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_20);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_8);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
}
else
{
lean_object* x_28; uint8_t x_29; 
lean_dec_ref(x_2);
x_28 = lean_apply_2(x_1, x_3, x_9);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_8);
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
lean_ctor_set(x_34, 1, x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
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
x_15 = l_Lake_checkHashUpToDate(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
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
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_18 = lean_ctor_get(x_8, 1);
x_19 = lean_ctor_get(x_8, 2);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_16);
lean_dec(x_8);
x_20 = lean_box(0);
x_21 = lean_array_push(x_16, x_2);
x_22 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_19);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_17);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_9);
return x_24;
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
lean_inc_ref(x_38);
lean_inc(x_34);
x_40 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_40, 0, x_34);
lean_closure_set(x_40, 1, x_38);
lean_inc(x_34);
lean_inc_ref(x_33);
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
lean_dec_ref(x_47);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_48 = lean_ctor_get(x_4, 2);
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
lean_dec_ref(x_47);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
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
lean_inc_ref(x_66);
lean_dec_ref(x_11);
x_67 = lean_ctor_get_uint8(x_66, sizeof(void*)*1);
lean_dec_ref(x_66);
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
lean_object* x_70; uint64_t x_71; lean_object* x_72; uint64_t x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_70 = lean_ctor_get(x_5, 0);
x_71 = lean_ctor_get_uint64(x_70, sizeof(void*)*3);
x_72 = lean_ctor_get(x_70, 2);
lean_inc_ref(x_72);
lean_dec_ref(x_70);
x_73 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_74 = lean_alloc_closure((void*)(l_Lake_SavedTrace_replayIfUpToDate___redArg___lam__0___boxed), 9, 0);
x_135 = lean_box_uint64(x_71);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_135);
x_136 = l_Lake_checkHashUpToDate___redArg___closed__0;
x_137 = lean_box_uint64(x_73);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_137);
x_139 = l_Option_beqOption___redArg____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3_(x_136, x_138, x_5);
if (x_139 == 0)
{
lean_object* x_140; uint8_t x_141; 
lean_dec_ref(x_1);
x_140 = lean_ctor_get(x_11, 0);
x_141 = lean_ctor_get_uint8(x_140, sizeof(void*)*1);
if (x_141 == 0)
{
lean_dec_ref(x_74);
lean_dec_ref(x_72);
lean_dec_ref(x_47);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_3);
lean_dec_ref(x_2);
x_14 = x_141;
x_15 = x_12;
x_16 = x_13;
goto block_20;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_142 = l_Lake_MTime_checkUpToDate___redArg(x_2, x_3, x_6, x_13);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec_ref(x_142);
x_145 = lean_unbox(x_143);
lean_dec(x_143);
x_75 = x_145;
x_76 = x_12;
x_77 = x_144;
goto block_134;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
lean_dec_ref(x_2);
x_146 = lean_apply_2(x_1, x_3, x_13);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec_ref(x_146);
x_149 = lean_unbox(x_147);
lean_dec(x_147);
x_75 = x_149;
x_76 = x_12;
x_77 = x_148;
goto block_134;
}
block_134:
{
if (x_75 == 0)
{
lean_dec_ref(x_74);
lean_dec_ref(x_72);
lean_dec_ref(x_47);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
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
uint8_t x_79; lean_object* x_80; uint8_t x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_79 = lean_ctor_get_uint8(x_76, sizeof(void*)*3);
x_80 = l_Lake_EquipT_instMonad___redArg(x_47);
x_81 = 1;
x_82 = l_Lake_JobAction_merge(x_79, x_81);
lean_ctor_set_uint8(x_76, sizeof(void*)*3, x_82);
x_83 = lean_unsigned_to_nat(0u);
x_84 = lean_array_get_size(x_72);
x_85 = lean_nat_dec_lt(x_83, x_84);
if (x_85 == 0)
{
lean_dec(x_84);
lean_dec_ref(x_80);
lean_dec_ref(x_74);
lean_dec_ref(x_72);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_21 = x_75;
x_22 = x_76;
x_23 = x_77;
goto block_27;
}
else
{
uint8_t x_86; 
x_86 = lean_nat_dec_le(x_84, x_84);
if (x_86 == 0)
{
lean_dec(x_84);
lean_dec_ref(x_80);
lean_dec_ref(x_74);
lean_dec_ref(x_72);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_21 = x_75;
x_22 = x_76;
x_23 = x_77;
goto block_27;
}
else
{
lean_object* x_87; size_t x_88; size_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_87 = lean_box(0);
x_88 = 0;
x_89 = lean_usize_of_nat(x_84);
lean_dec(x_84);
x_90 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_80, x_74, x_72, x_88, x_89, x_87);
x_91 = lean_apply_7(x_90, x_7, x_8, x_9, x_10, x_11, x_76, x_77);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec_ref(x_91);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec_ref(x_92);
x_21 = x_75;
x_22 = x_94;
x_23 = x_93;
goto block_27;
}
else
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_91);
if (x_95 == 0)
{
lean_object* x_96; uint8_t x_97; 
x_96 = lean_ctor_get(x_91, 0);
lean_dec(x_96);
x_97 = !lean_is_exclusive(x_92);
if (x_97 == 0)
{
return x_91;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_92, 0);
x_99 = lean_ctor_get(x_92, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_92);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
lean_ctor_set(x_91, 0, x_100);
return x_91;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_101 = lean_ctor_get(x_91, 1);
lean_inc(x_101);
lean_dec(x_91);
x_102 = lean_ctor_get(x_92, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_92, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_104 = x_92;
} else {
 lean_dec_ref(x_92);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_101);
return x_106;
}
}
}
}
}
else
{
lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_107 = lean_ctor_get(x_76, 0);
x_108 = lean_ctor_get_uint8(x_76, sizeof(void*)*3);
x_109 = lean_ctor_get(x_76, 1);
x_110 = lean_ctor_get(x_76, 2);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_107);
lean_dec(x_76);
x_111 = l_Lake_EquipT_instMonad___redArg(x_47);
x_112 = 1;
x_113 = l_Lake_JobAction_merge(x_108, x_112);
x_114 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_114, 0, x_107);
lean_ctor_set(x_114, 1, x_109);
lean_ctor_set(x_114, 2, x_110);
lean_ctor_set_uint8(x_114, sizeof(void*)*3, x_113);
x_115 = lean_unsigned_to_nat(0u);
x_116 = lean_array_get_size(x_72);
x_117 = lean_nat_dec_lt(x_115, x_116);
if (x_117 == 0)
{
lean_dec(x_116);
lean_dec_ref(x_111);
lean_dec_ref(x_74);
lean_dec_ref(x_72);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_21 = x_75;
x_22 = x_114;
x_23 = x_77;
goto block_27;
}
else
{
uint8_t x_118; 
x_118 = lean_nat_dec_le(x_116, x_116);
if (x_118 == 0)
{
lean_dec(x_116);
lean_dec_ref(x_111);
lean_dec_ref(x_74);
lean_dec_ref(x_72);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_21 = x_75;
x_22 = x_114;
x_23 = x_77;
goto block_27;
}
else
{
lean_object* x_119; size_t x_120; size_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_119 = lean_box(0);
x_120 = 0;
x_121 = lean_usize_of_nat(x_116);
lean_dec(x_116);
x_122 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_111, x_74, x_72, x_120, x_121, x_119);
x_123 = lean_apply_7(x_122, x_7, x_8, x_9, x_10, x_11, x_114, x_77);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec_ref(x_123);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec_ref(x_124);
x_21 = x_75;
x_22 = x_126;
x_23 = x_125;
goto block_27;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_127 = lean_ctor_get(x_123, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_128 = x_123;
} else {
 lean_dec_ref(x_123);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_124, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_124, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_131 = x_124;
} else {
 lean_dec_ref(x_124);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(1, 2, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_130);
if (lean_is_scalar(x_128)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_128;
}
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_127);
return x_133;
}
}
}
}
}
}
}
else
{
lean_object* x_150; uint64_t x_151; lean_object* x_152; uint64_t x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_150 = lean_ctor_get(x_5, 0);
lean_inc(x_150);
lean_dec(x_5);
x_151 = lean_ctor_get_uint64(x_150, sizeof(void*)*3);
x_152 = lean_ctor_get(x_150, 2);
lean_inc_ref(x_152);
lean_dec_ref(x_150);
x_153 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_154 = lean_alloc_closure((void*)(l_Lake_SavedTrace_replayIfUpToDate___redArg___lam__0___boxed), 9, 0);
x_187 = lean_box_uint64(x_151);
x_188 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_188, 0, x_187);
x_189 = l_Lake_checkHashUpToDate___redArg___closed__0;
x_190 = lean_box_uint64(x_153);
x_191 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_191, 0, x_190);
x_192 = l_Option_beqOption___redArg____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3_(x_189, x_191, x_188);
if (x_192 == 0)
{
lean_object* x_193; uint8_t x_194; 
lean_dec_ref(x_1);
x_193 = lean_ctor_get(x_11, 0);
x_194 = lean_ctor_get_uint8(x_193, sizeof(void*)*1);
if (x_194 == 0)
{
lean_dec_ref(x_154);
lean_dec_ref(x_152);
lean_dec_ref(x_47);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_3);
lean_dec_ref(x_2);
x_14 = x_194;
x_15 = x_12;
x_16 = x_13;
goto block_20;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_195 = l_Lake_MTime_checkUpToDate___redArg(x_2, x_3, x_6, x_13);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec_ref(x_195);
x_198 = lean_unbox(x_196);
lean_dec(x_196);
x_155 = x_198;
x_156 = x_12;
x_157 = x_197;
goto block_186;
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
lean_dec_ref(x_2);
x_199 = lean_apply_2(x_1, x_3, x_13);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec_ref(x_199);
x_202 = lean_unbox(x_200);
lean_dec(x_200);
x_155 = x_202;
x_156 = x_12;
x_157 = x_201;
goto block_186;
}
block_186:
{
if (x_155 == 0)
{
lean_dec_ref(x_154);
lean_dec_ref(x_152);
lean_dec_ref(x_47);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_14 = x_155;
x_15 = x_156;
x_16 = x_157;
goto block_20;
}
else
{
lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; uint8_t x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_158 = lean_ctor_get(x_156, 0);
lean_inc_ref(x_158);
x_159 = lean_ctor_get_uint8(x_156, sizeof(void*)*3);
x_160 = lean_ctor_get(x_156, 1);
lean_inc_ref(x_160);
x_161 = lean_ctor_get(x_156, 2);
lean_inc(x_161);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 lean_ctor_release(x_156, 2);
 x_162 = x_156;
} else {
 lean_dec_ref(x_156);
 x_162 = lean_box(0);
}
x_163 = l_Lake_EquipT_instMonad___redArg(x_47);
x_164 = 1;
x_165 = l_Lake_JobAction_merge(x_159, x_164);
if (lean_is_scalar(x_162)) {
 x_166 = lean_alloc_ctor(0, 3, 1);
} else {
 x_166 = x_162;
}
lean_ctor_set(x_166, 0, x_158);
lean_ctor_set(x_166, 1, x_160);
lean_ctor_set(x_166, 2, x_161);
lean_ctor_set_uint8(x_166, sizeof(void*)*3, x_165);
x_167 = lean_unsigned_to_nat(0u);
x_168 = lean_array_get_size(x_152);
x_169 = lean_nat_dec_lt(x_167, x_168);
if (x_169 == 0)
{
lean_dec(x_168);
lean_dec_ref(x_163);
lean_dec_ref(x_154);
lean_dec_ref(x_152);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_21 = x_155;
x_22 = x_166;
x_23 = x_157;
goto block_27;
}
else
{
uint8_t x_170; 
x_170 = lean_nat_dec_le(x_168, x_168);
if (x_170 == 0)
{
lean_dec(x_168);
lean_dec_ref(x_163);
lean_dec_ref(x_154);
lean_dec_ref(x_152);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_21 = x_155;
x_22 = x_166;
x_23 = x_157;
goto block_27;
}
else
{
lean_object* x_171; size_t x_172; size_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_171 = lean_box(0);
x_172 = 0;
x_173 = lean_usize_of_nat(x_168);
lean_dec(x_168);
x_174 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_163, x_154, x_152, x_172, x_173, x_171);
x_175 = lean_apply_7(x_174, x_7, x_8, x_9, x_10, x_11, x_166, x_157);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec_ref(x_175);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec_ref(x_176);
x_21 = x_155;
x_22 = x_178;
x_23 = x_177;
goto block_27;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
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
x_181 = lean_ctor_get(x_176, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_176, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_183 = x_176;
} else {
 lean_dec_ref(x_176);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_182);
if (lean_is_scalar(x_180)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_180;
}
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_179);
return x_185;
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
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_203 = lean_ctor_get(x_28, 1);
x_204 = lean_ctor_get(x_30, 0);
x_205 = lean_ctor_get(x_30, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_30);
lean_inc(x_203);
lean_inc(x_205);
x_206 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_206, 0, x_205);
lean_closure_set(x_206, 1, x_203);
lean_inc(x_203);
lean_inc(x_205);
x_207 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_207, 0, x_205);
lean_closure_set(x_207, 1, x_203);
lean_inc_ref(x_206);
lean_inc(x_205);
x_208 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_208, 0, x_205);
lean_closure_set(x_208, 1, x_206);
lean_inc(x_205);
lean_inc_ref(x_204);
x_209 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_209, 0, x_204);
lean_closure_set(x_209, 1, x_205);
lean_closure_set(x_209, 2, x_203);
x_210 = l_Lake_EStateT_instFunctor___redArg(x_204);
x_211 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_211, 0, x_205);
x_212 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
lean_ctor_set(x_212, 2, x_209);
lean_ctor_set(x_212, 3, x_208);
lean_ctor_set(x_212, 4, x_207);
lean_ctor_set(x_28, 1, x_206);
lean_ctor_set(x_28, 0, x_212);
x_213 = l_ReaderT_instMonad___redArg(x_28);
x_214 = l_ReaderT_instMonad___redArg(x_213);
x_215 = l_ReaderT_instMonad___redArg(x_214);
x_216 = l_ReaderT_instMonad___redArg(x_215);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec_ref(x_216);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_217 = lean_ctor_get(x_4, 2);
x_218 = l_Lake_MTime_checkUpToDate___redArg(x_2, x_3, x_217, x_13);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_221 = x_218;
} else {
 lean_dec_ref(x_218);
 x_221 = lean_box(0);
}
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_219);
lean_ctor_set(x_222, 1, x_12);
if (lean_is_scalar(x_221)) {
 x_223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_223 = x_221;
}
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_220);
return x_223;
}
case 1:
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; lean_object* x_233; uint8_t x_234; 
lean_dec_ref(x_216);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_224 = l_Lake_MTime_checkUpToDate___redArg(x_2, x_3, x_6, x_13);
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_227 = x_224;
} else {
 lean_dec_ref(x_224);
 x_227 = lean_box(0);
}
x_233 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_233);
lean_dec_ref(x_11);
x_234 = lean_ctor_get_uint8(x_233, sizeof(void*)*1);
lean_dec_ref(x_233);
if (x_234 == 0)
{
lean_dec(x_225);
x_228 = x_234;
goto block_232;
}
else
{
uint8_t x_235; 
x_235 = lean_unbox(x_225);
lean_dec(x_225);
x_228 = x_235;
goto block_232;
}
block_232:
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_box(x_228);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_12);
if (lean_is_scalar(x_227)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_227;
}
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_226);
return x_231;
}
}
default: 
{
lean_object* x_236; lean_object* x_237; uint64_t x_238; lean_object* x_239; uint64_t x_240; lean_object* x_241; uint8_t x_242; lean_object* x_243; lean_object* x_244; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; uint8_t x_279; 
x_236 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_236);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_237 = x_5;
} else {
 lean_dec_ref(x_5);
 x_237 = lean_box(0);
}
x_238 = lean_ctor_get_uint64(x_236, sizeof(void*)*3);
x_239 = lean_ctor_get(x_236, 2);
lean_inc_ref(x_239);
lean_dec_ref(x_236);
x_240 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_241 = lean_alloc_closure((void*)(l_Lake_SavedTrace_replayIfUpToDate___redArg___lam__0___boxed), 9, 0);
x_274 = lean_box_uint64(x_238);
if (lean_is_scalar(x_237)) {
 x_275 = lean_alloc_ctor(1, 1, 0);
} else {
 x_275 = x_237;
 lean_ctor_set_tag(x_275, 1);
}
lean_ctor_set(x_275, 0, x_274);
x_276 = l_Lake_checkHashUpToDate___redArg___closed__0;
x_277 = lean_box_uint64(x_240);
x_278 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_278, 0, x_277);
x_279 = l_Option_beqOption___redArg____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3_(x_276, x_278, x_275);
if (x_279 == 0)
{
lean_object* x_280; uint8_t x_281; 
lean_dec_ref(x_1);
x_280 = lean_ctor_get(x_11, 0);
x_281 = lean_ctor_get_uint8(x_280, sizeof(void*)*1);
if (x_281 == 0)
{
lean_dec_ref(x_241);
lean_dec_ref(x_239);
lean_dec_ref(x_216);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_3);
lean_dec_ref(x_2);
x_14 = x_281;
x_15 = x_12;
x_16 = x_13;
goto block_20;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; 
x_282 = l_Lake_MTime_checkUpToDate___redArg(x_2, x_3, x_6, x_13);
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
lean_dec_ref(x_282);
x_285 = lean_unbox(x_283);
lean_dec(x_283);
x_242 = x_285;
x_243 = x_12;
x_244 = x_284;
goto block_273;
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; 
lean_dec_ref(x_2);
x_286 = lean_apply_2(x_1, x_3, x_13);
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec_ref(x_286);
x_289 = lean_unbox(x_287);
lean_dec(x_287);
x_242 = x_289;
x_243 = x_12;
x_244 = x_288;
goto block_273;
}
block_273:
{
if (x_242 == 0)
{
lean_dec_ref(x_241);
lean_dec_ref(x_239);
lean_dec_ref(x_216);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_14 = x_242;
x_15 = x_243;
x_16 = x_244;
goto block_20;
}
else
{
lean_object* x_245; uint8_t x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; uint8_t x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; 
x_245 = lean_ctor_get(x_243, 0);
lean_inc_ref(x_245);
x_246 = lean_ctor_get_uint8(x_243, sizeof(void*)*3);
x_247 = lean_ctor_get(x_243, 1);
lean_inc_ref(x_247);
x_248 = lean_ctor_get(x_243, 2);
lean_inc(x_248);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 lean_ctor_release(x_243, 2);
 x_249 = x_243;
} else {
 lean_dec_ref(x_243);
 x_249 = lean_box(0);
}
x_250 = l_Lake_EquipT_instMonad___redArg(x_216);
x_251 = 1;
x_252 = l_Lake_JobAction_merge(x_246, x_251);
if (lean_is_scalar(x_249)) {
 x_253 = lean_alloc_ctor(0, 3, 1);
} else {
 x_253 = x_249;
}
lean_ctor_set(x_253, 0, x_245);
lean_ctor_set(x_253, 1, x_247);
lean_ctor_set(x_253, 2, x_248);
lean_ctor_set_uint8(x_253, sizeof(void*)*3, x_252);
x_254 = lean_unsigned_to_nat(0u);
x_255 = lean_array_get_size(x_239);
x_256 = lean_nat_dec_lt(x_254, x_255);
if (x_256 == 0)
{
lean_dec(x_255);
lean_dec_ref(x_250);
lean_dec_ref(x_241);
lean_dec_ref(x_239);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_21 = x_242;
x_22 = x_253;
x_23 = x_244;
goto block_27;
}
else
{
uint8_t x_257; 
x_257 = lean_nat_dec_le(x_255, x_255);
if (x_257 == 0)
{
lean_dec(x_255);
lean_dec_ref(x_250);
lean_dec_ref(x_241);
lean_dec_ref(x_239);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_21 = x_242;
x_22 = x_253;
x_23 = x_244;
goto block_27;
}
else
{
lean_object* x_258; size_t x_259; size_t x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_258 = lean_box(0);
x_259 = 0;
x_260 = lean_usize_of_nat(x_255);
lean_dec(x_255);
x_261 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_250, x_241, x_239, x_259, x_260, x_258);
x_262 = lean_apply_7(x_261, x_7, x_8, x_9, x_10, x_11, x_253, x_244);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; 
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec_ref(x_262);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
lean_dec_ref(x_263);
x_21 = x_242;
x_22 = x_265;
x_23 = x_264;
goto block_27;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_266 = lean_ctor_get(x_262, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_267 = x_262;
} else {
 lean_dec_ref(x_262);
 x_267 = lean_box(0);
}
x_268 = lean_ctor_get(x_263, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_263, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_270 = x_263;
} else {
 lean_dec_ref(x_263);
 x_270 = lean_box(0);
}
if (lean_is_scalar(x_270)) {
 x_271 = lean_alloc_ctor(1, 2, 0);
} else {
 x_271 = x_270;
}
lean_ctor_set(x_271, 0, x_268);
lean_ctor_set(x_271, 1, x_269);
if (lean_is_scalar(x_267)) {
 x_272 = lean_alloc_ctor(0, 2, 0);
} else {
 x_272 = x_267;
}
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_266);
return x_272;
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
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_290 = lean_ctor_get(x_28, 0);
x_291 = lean_ctor_get(x_28, 1);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_28);
x_292 = lean_ctor_get(x_290, 0);
lean_inc_ref(x_292);
x_293 = lean_ctor_get(x_290, 1);
lean_inc(x_293);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 lean_ctor_release(x_290, 1);
 lean_ctor_release(x_290, 2);
 lean_ctor_release(x_290, 3);
 lean_ctor_release(x_290, 4);
 x_294 = x_290;
} else {
 lean_dec_ref(x_290);
 x_294 = lean_box(0);
}
lean_inc(x_291);
lean_inc(x_293);
x_295 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_295, 0, x_293);
lean_closure_set(x_295, 1, x_291);
lean_inc(x_291);
lean_inc(x_293);
x_296 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_296, 0, x_293);
lean_closure_set(x_296, 1, x_291);
lean_inc_ref(x_295);
lean_inc(x_293);
x_297 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_297, 0, x_293);
lean_closure_set(x_297, 1, x_295);
lean_inc(x_293);
lean_inc_ref(x_292);
x_298 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_298, 0, x_292);
lean_closure_set(x_298, 1, x_293);
lean_closure_set(x_298, 2, x_291);
x_299 = l_Lake_EStateT_instFunctor___redArg(x_292);
x_300 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_300, 0, x_293);
if (lean_is_scalar(x_294)) {
 x_301 = lean_alloc_ctor(0, 5, 0);
} else {
 x_301 = x_294;
}
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
lean_ctor_set(x_301, 2, x_298);
lean_ctor_set(x_301, 3, x_297);
lean_ctor_set(x_301, 4, x_296);
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_295);
x_303 = l_ReaderT_instMonad___redArg(x_302);
x_304 = l_ReaderT_instMonad___redArg(x_303);
x_305 = l_ReaderT_instMonad___redArg(x_304);
x_306 = l_ReaderT_instMonad___redArg(x_305);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec_ref(x_306);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_307 = lean_ctor_get(x_4, 2);
x_308 = l_Lake_MTime_checkUpToDate___redArg(x_2, x_3, x_307, x_13);
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_308, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_308)) {
 lean_ctor_release(x_308, 0);
 lean_ctor_release(x_308, 1);
 x_311 = x_308;
} else {
 lean_dec_ref(x_308);
 x_311 = lean_box(0);
}
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_309);
lean_ctor_set(x_312, 1, x_12);
if (lean_is_scalar(x_311)) {
 x_313 = lean_alloc_ctor(0, 2, 0);
} else {
 x_313 = x_311;
}
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_310);
return x_313;
}
case 1:
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; lean_object* x_323; uint8_t x_324; 
lean_dec_ref(x_306);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_314 = l_Lake_MTime_checkUpToDate___redArg(x_2, x_3, x_6, x_13);
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 lean_ctor_release(x_314, 1);
 x_317 = x_314;
} else {
 lean_dec_ref(x_314);
 x_317 = lean_box(0);
}
x_323 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_323);
lean_dec_ref(x_11);
x_324 = lean_ctor_get_uint8(x_323, sizeof(void*)*1);
lean_dec_ref(x_323);
if (x_324 == 0)
{
lean_dec(x_315);
x_318 = x_324;
goto block_322;
}
else
{
uint8_t x_325; 
x_325 = lean_unbox(x_315);
lean_dec(x_315);
x_318 = x_325;
goto block_322;
}
block_322:
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_319 = lean_box(x_318);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_12);
if (lean_is_scalar(x_317)) {
 x_321 = lean_alloc_ctor(0, 2, 0);
} else {
 x_321 = x_317;
}
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_316);
return x_321;
}
}
default: 
{
lean_object* x_326; lean_object* x_327; uint64_t x_328; lean_object* x_329; uint64_t x_330; lean_object* x_331; uint8_t x_332; lean_object* x_333; lean_object* x_334; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; 
x_326 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_326);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_327 = x_5;
} else {
 lean_dec_ref(x_5);
 x_327 = lean_box(0);
}
x_328 = lean_ctor_get_uint64(x_326, sizeof(void*)*3);
x_329 = lean_ctor_get(x_326, 2);
lean_inc_ref(x_329);
lean_dec_ref(x_326);
x_330 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_331 = lean_alloc_closure((void*)(l_Lake_SavedTrace_replayIfUpToDate___redArg___lam__0___boxed), 9, 0);
x_364 = lean_box_uint64(x_328);
if (lean_is_scalar(x_327)) {
 x_365 = lean_alloc_ctor(1, 1, 0);
} else {
 x_365 = x_327;
 lean_ctor_set_tag(x_365, 1);
}
lean_ctor_set(x_365, 0, x_364);
x_366 = l_Lake_checkHashUpToDate___redArg___closed__0;
x_367 = lean_box_uint64(x_330);
x_368 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_368, 0, x_367);
x_369 = l_Option_beqOption___redArg____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3_(x_366, x_368, x_365);
if (x_369 == 0)
{
lean_object* x_370; uint8_t x_371; 
lean_dec_ref(x_1);
x_370 = lean_ctor_get(x_11, 0);
x_371 = lean_ctor_get_uint8(x_370, sizeof(void*)*1);
if (x_371 == 0)
{
lean_dec_ref(x_331);
lean_dec_ref(x_329);
lean_dec_ref(x_306);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_3);
lean_dec_ref(x_2);
x_14 = x_371;
x_15 = x_12;
x_16 = x_13;
goto block_20;
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; uint8_t x_375; 
x_372 = l_Lake_MTime_checkUpToDate___redArg(x_2, x_3, x_6, x_13);
x_373 = lean_ctor_get(x_372, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_372, 1);
lean_inc(x_374);
lean_dec_ref(x_372);
x_375 = lean_unbox(x_373);
lean_dec(x_373);
x_332 = x_375;
x_333 = x_12;
x_334 = x_374;
goto block_363;
}
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; uint8_t x_379; 
lean_dec_ref(x_2);
x_376 = lean_apply_2(x_1, x_3, x_13);
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_376, 1);
lean_inc(x_378);
lean_dec_ref(x_376);
x_379 = lean_unbox(x_377);
lean_dec(x_377);
x_332 = x_379;
x_333 = x_12;
x_334 = x_378;
goto block_363;
}
block_363:
{
if (x_332 == 0)
{
lean_dec_ref(x_331);
lean_dec_ref(x_329);
lean_dec_ref(x_306);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_14 = x_332;
x_15 = x_333;
x_16 = x_334;
goto block_20;
}
else
{
lean_object* x_335; uint8_t x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; uint8_t x_341; uint8_t x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; 
x_335 = lean_ctor_get(x_333, 0);
lean_inc_ref(x_335);
x_336 = lean_ctor_get_uint8(x_333, sizeof(void*)*3);
x_337 = lean_ctor_get(x_333, 1);
lean_inc_ref(x_337);
x_338 = lean_ctor_get(x_333, 2);
lean_inc(x_338);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 lean_ctor_release(x_333, 2);
 x_339 = x_333;
} else {
 lean_dec_ref(x_333);
 x_339 = lean_box(0);
}
x_340 = l_Lake_EquipT_instMonad___redArg(x_306);
x_341 = 1;
x_342 = l_Lake_JobAction_merge(x_336, x_341);
if (lean_is_scalar(x_339)) {
 x_343 = lean_alloc_ctor(0, 3, 1);
} else {
 x_343 = x_339;
}
lean_ctor_set(x_343, 0, x_335);
lean_ctor_set(x_343, 1, x_337);
lean_ctor_set(x_343, 2, x_338);
lean_ctor_set_uint8(x_343, sizeof(void*)*3, x_342);
x_344 = lean_unsigned_to_nat(0u);
x_345 = lean_array_get_size(x_329);
x_346 = lean_nat_dec_lt(x_344, x_345);
if (x_346 == 0)
{
lean_dec(x_345);
lean_dec_ref(x_340);
lean_dec_ref(x_331);
lean_dec_ref(x_329);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_21 = x_332;
x_22 = x_343;
x_23 = x_334;
goto block_27;
}
else
{
uint8_t x_347; 
x_347 = lean_nat_dec_le(x_345, x_345);
if (x_347 == 0)
{
lean_dec(x_345);
lean_dec_ref(x_340);
lean_dec_ref(x_331);
lean_dec_ref(x_329);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_21 = x_332;
x_22 = x_343;
x_23 = x_334;
goto block_27;
}
else
{
lean_object* x_348; size_t x_349; size_t x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_348 = lean_box(0);
x_349 = 0;
x_350 = lean_usize_of_nat(x_345);
lean_dec(x_345);
x_351 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_340, x_331, x_329, x_349, x_350, x_348);
x_352 = lean_apply_7(x_351, x_7, x_8, x_9, x_10, x_11, x_343, x_334);
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; lean_object* x_355; 
x_354 = lean_ctor_get(x_352, 1);
lean_inc(x_354);
lean_dec_ref(x_352);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
lean_dec_ref(x_353);
x_21 = x_332;
x_22 = x_355;
x_23 = x_354;
goto block_27;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_356 = lean_ctor_get(x_352, 1);
lean_inc(x_356);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 x_357 = x_352;
} else {
 lean_dec_ref(x_352);
 x_357 = lean_box(0);
}
x_358 = lean_ctor_get(x_353, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_353, 1);
lean_inc(x_359);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 x_360 = x_353;
} else {
 lean_dec_ref(x_353);
 x_360 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_361 = lean_alloc_ctor(1, 2, 0);
} else {
 x_361 = x_360;
}
lean_ctor_set(x_361, 0, x_358);
lean_ctor_set(x_361, 1, x_359);
if (lean_is_scalar(x_357)) {
 x_362 = lean_alloc_ctor(0, 2, 0);
} else {
 x_362 = x_357;
}
lean_ctor_set(x_362, 0, x_361);
lean_ctor_set(x_362, 1, x_356);
return x_362;
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
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lake_SavedTrace_replayIfUpToDate___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lake_SavedTrace_replayIfUpToDate(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayOrFetch_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayOrFetch_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayOrFetch_spec__0___redArg(x_1, x_2, x_3, x_4, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetch(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_4) == 2)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_3);
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_12, 2);
x_14 = lean_ctor_get_uint8(x_12, sizeof(void*)*3 + 8);
if (x_14 == 0)
{
goto block_50;
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_array_get_size(x_13);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_nat_dec_eq(x_51, x_52);
lean_dec(x_51);
if (x_53 == 0)
{
goto block_50;
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_10);
if (x_54 == 0)
{
uint8_t x_55; uint8_t x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
x_56 = 2;
x_57 = lean_box(0);
x_58 = l_Lake_JobAction_merge(x_55, x_56);
lean_ctor_set_uint8(x_10, sizeof(void*)*3, x_58);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_10);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_11);
return x_60;
}
else
{
lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_61 = lean_ctor_get(x_10, 0);
x_62 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
x_63 = lean_ctor_get(x_10, 1);
x_64 = lean_ctor_get(x_10, 2);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_61);
lean_dec(x_10);
x_65 = 2;
x_66 = lean_box(0);
x_67 = l_Lake_JobAction_merge(x_62, x_65);
x_68 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_68, 0, x_61);
lean_ctor_set(x_68, 1, x_63);
lean_ctor_set(x_68, 2, x_64);
lean_ctor_set_uint8(x_68, sizeof(void*)*3, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_11);
return x_70;
}
}
}
block_50:
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_16 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
x_17 = 1;
x_18 = l_Lake_JobAction_merge(x_16, x_17);
lean_ctor_set_uint8(x_10, sizeof(void*)*3, x_18);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_get_size(x_13);
x_21 = lean_box(0);
x_22 = lean_nat_dec_lt(x_19, x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_10);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_11);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_20, x_20);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_20);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_10);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_11);
return x_27;
}
else
{
size_t x_28; size_t x_29; lean_object* x_30; 
x_28 = 0;
x_29 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_30 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayOrFetch_spec__0___redArg(x_13, x_28, x_29, x_21, x_10, x_11);
return x_30;
}
}
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_31 = lean_ctor_get(x_10, 0);
x_32 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
x_33 = lean_ctor_get(x_10, 1);
x_34 = lean_ctor_get(x_10, 2);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_31);
lean_dec(x_10);
x_35 = 1;
x_36 = l_Lake_JobAction_merge(x_32, x_35);
x_37 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_33);
lean_ctor_set(x_37, 2, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*3, x_36);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_array_get_size(x_13);
x_40 = lean_box(0);
x_41 = lean_nat_dec_lt(x_38, x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_37);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_11);
return x_43;
}
else
{
uint8_t x_44; 
x_44 = lean_nat_dec_le(x_39, x_39);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_39);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_37);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_11);
return x_46;
}
else
{
size_t x_47; size_t x_48; lean_object* x_49; 
x_47 = 0;
x_48 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_49 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayOrFetch_spec__0___redArg(x_13, x_47, x_48, x_40, x_37, x_11);
return x_49;
}
}
}
}
}
else
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_10);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; 
x_72 = lean_ctor_get(x_10, 0);
x_73 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
x_74 = 2;
x_75 = l_Lake_JobAction_merge(x_73, x_74);
x_76 = l_Lake_BuildMetadata_ofFetch(x_2, x_3);
x_77 = l_Lake_BuildMetadata_writeFile(x_1, x_76, x_11);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_77, 0);
lean_ctor_set_uint8(x_10, sizeof(void*)*3, x_75);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_10);
lean_ctor_set(x_77, 0, x_80);
return x_77;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_77, 0);
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_77);
lean_ctor_set_uint8(x_10, sizeof(void*)*3, x_75);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_10);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_77);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_86 = lean_ctor_get(x_77, 0);
x_87 = lean_io_error_to_string(x_86);
x_88 = 3;
x_89 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set_uint8(x_89, sizeof(void*)*1, x_88);
x_90 = lean_array_get_size(x_72);
x_91 = lean_array_push(x_72, x_89);
lean_ctor_set(x_10, 0, x_91);
lean_ctor_set_uint8(x_10, sizeof(void*)*3, x_75);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_10);
lean_ctor_set_tag(x_77, 0);
lean_ctor_set(x_77, 0, x_92);
return x_77;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_93 = lean_ctor_get(x_77, 0);
x_94 = lean_ctor_get(x_77, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_77);
x_95 = lean_io_error_to_string(x_93);
x_96 = 3;
x_97 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set_uint8(x_97, sizeof(void*)*1, x_96);
x_98 = lean_array_get_size(x_72);
x_99 = lean_array_push(x_72, x_97);
lean_ctor_set(x_10, 0, x_99);
lean_ctor_set_uint8(x_10, sizeof(void*)*3, x_75);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_10);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_94);
return x_101;
}
}
}
else
{
lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; 
x_102 = lean_ctor_get(x_10, 0);
x_103 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
x_104 = lean_ctor_get(x_10, 1);
x_105 = lean_ctor_get(x_10, 2);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_102);
lean_dec(x_10);
x_106 = 2;
x_107 = l_Lake_JobAction_merge(x_103, x_106);
x_108 = l_Lake_BuildMetadata_ofFetch(x_2, x_3);
x_109 = l_Lake_BuildMetadata_writeFile(x_1, x_108, x_11);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_112 = x_109;
} else {
 lean_dec_ref(x_109);
 x_112 = lean_box(0);
}
x_113 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_113, 0, x_102);
lean_ctor_set(x_113, 1, x_104);
lean_ctor_set(x_113, 2, x_105);
lean_ctor_set_uint8(x_113, sizeof(void*)*3, x_107);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_110);
lean_ctor_set(x_114, 1, x_113);
if (lean_is_scalar(x_112)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_112;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_111);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_116 = lean_ctor_get(x_109, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_109, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_118 = x_109;
} else {
 lean_dec_ref(x_109);
 x_118 = lean_box(0);
}
x_119 = lean_io_error_to_string(x_116);
x_120 = 3;
x_121 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set_uint8(x_121, sizeof(void*)*1, x_120);
x_122 = lean_array_get_size(x_102);
x_123 = lean_array_push(x_102, x_121);
x_124 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_104);
lean_ctor_set(x_124, 2, x_105);
lean_ctor_set_uint8(x_124, sizeof(void*)*3, x_107);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_124);
if (lean_is_scalar(x_118)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_118;
 lean_ctor_set_tag(x_126, 0);
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_117);
return x_126;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayOrFetch_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayOrFetch_spec__0___redArg(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayOrFetch_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayOrFetch_spec__0(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayOrFetch___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint64_t x_12; lean_object* x_13; 
x_12 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_13 = l_Lake_SavedTrace_replayOrFetch(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get_uint8(x_19, sizeof(void*)*1 + 2);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_24 = lean_io_mono_ms_now(x_12);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = l_Lake_JobAction_merge(x_23, x_5);
lean_inc_ref(x_22);
lean_ctor_set_uint8(x_11, sizeof(void*)*3, x_27);
x_28 = lean_apply_7(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_26);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_40 = lean_ctor_get(x_29, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_29, 0);
lean_inc(x_41);
lean_dec_ref(x_29);
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get_uint8(x_40, sizeof(void*)*3);
x_44 = lean_ctor_get(x_40, 1);
x_45 = lean_ctor_get(x_40, 2);
x_46 = lean_array_get_size(x_22);
lean_dec_ref(x_22);
x_47 = lean_array_get_size(x_42);
lean_inc(x_47);
x_48 = l_Array_extract___redArg(x_42, x_46, x_47);
lean_inc(x_41);
x_49 = lean_apply_1(x_1, x_41);
x_50 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_2, x_49, x_48);
x_51 = l_Lake_BuildMetadata_writeFile(x_3, x_50, x_30);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
lean_dec(x_47);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_53 = lean_ctor_get(x_51, 1);
x_54 = lean_ctor_get(x_51, 0);
lean_dec(x_54);
x_55 = lean_box(0);
lean_inc(x_41);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 1, x_55);
lean_ctor_set(x_51, 0, x_41);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_51);
x_57 = l_Lake_buildAction___redArg___lam__0(x_25, x_56, x_40, x_53);
lean_dec_ref(x_56);
lean_dec(x_25);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_59, 0);
lean_dec(x_61);
lean_ctor_set(x_59, 0, x_41);
return x_57;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_41);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_57, 0, x_63);
return x_57;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_57, 0);
x_65 = lean_ctor_get(x_57, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_57);
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
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_41);
lean_ctor_set(x_68, 1, x_66);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_65);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_70 = lean_ctor_get(x_51, 1);
lean_inc(x_70);
lean_dec(x_51);
x_71 = lean_box(0);
lean_inc(x_41);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_41);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = l_Lake_buildAction___redArg___lam__0(x_25, x_73, x_40, x_70);
lean_dec_ref(x_73);
lean_dec(x_25);
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
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_41);
lean_ctor_set(x_80, 1, x_78);
if (lean_is_scalar(x_77)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_77;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_76);
return x_81;
}
}
else
{
uint8_t x_82; 
lean_inc(x_45);
lean_inc_ref(x_44);
lean_inc_ref(x_42);
lean_dec(x_41);
x_82 = !lean_is_exclusive(x_40);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; 
x_83 = lean_ctor_get(x_40, 2);
lean_dec(x_83);
x_84 = lean_ctor_get(x_40, 1);
lean_dec(x_84);
x_85 = lean_ctor_get(x_40, 0);
lean_dec(x_85);
x_86 = lean_ctor_get(x_51, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_51, 1);
lean_inc(x_87);
lean_dec_ref(x_51);
x_88 = lean_io_error_to_string(x_86);
x_89 = 3;
x_90 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set_uint8(x_90, sizeof(void*)*1, x_89);
x_91 = lean_array_push(x_42, x_90);
lean_ctor_set(x_40, 0, x_91);
x_31 = x_47;
x_32 = x_40;
x_33 = x_87;
goto block_39;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_40);
x_92 = lean_ctor_get(x_51, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_51, 1);
lean_inc(x_93);
lean_dec_ref(x_51);
x_94 = lean_io_error_to_string(x_92);
x_95 = 3;
x_96 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set_uint8(x_96, sizeof(void*)*1, x_95);
x_97 = lean_array_push(x_42, x_96);
x_98 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_44);
lean_ctor_set(x_98, 2, x_45);
lean_ctor_set_uint8(x_98, sizeof(void*)*3, x_43);
x_31 = x_47;
x_32 = x_98;
x_33 = x_93;
goto block_39;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; 
lean_dec_ref(x_22);
lean_dec_ref(x_1);
x_99 = lean_ctor_get(x_29, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_29, 1);
lean_inc(x_100);
lean_dec_ref(x_29);
x_31 = x_99;
x_32 = x_100;
x_33 = x_30;
goto block_39;
}
block_39:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_box(0);
x_35 = l_Lake_buildAction___redArg___lam__0(x_25, x_34, x_32, x_33);
lean_dec(x_25);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_13 = x_31;
x_14 = x_38;
x_15 = x_37;
goto block_18;
}
}
else
{
lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_101 = lean_ctor_get(x_11, 0);
x_102 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_103 = lean_ctor_get(x_11, 1);
x_104 = lean_ctor_get(x_11, 2);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_101);
lean_dec(x_11);
x_105 = lean_io_mono_ms_now(x_12);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec_ref(x_105);
x_108 = l_Lake_JobAction_merge(x_102, x_5);
lean_inc_ref(x_101);
x_109 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_109, 0, x_101);
lean_ctor_set(x_109, 1, x_103);
lean_ctor_set(x_109, 2, x_104);
lean_ctor_set_uint8(x_109, sizeof(void*)*3, x_108);
x_110 = lean_apply_7(x_4, x_6, x_7, x_8, x_9, x_10, x_109, x_107);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec_ref(x_110);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_122 = lean_ctor_get(x_111, 1);
lean_inc(x_122);
x_123 = lean_ctor_get(x_111, 0);
lean_inc(x_123);
lean_dec_ref(x_111);
x_124 = lean_ctor_get(x_122, 0);
x_125 = lean_ctor_get_uint8(x_122, sizeof(void*)*3);
x_126 = lean_ctor_get(x_122, 1);
x_127 = lean_ctor_get(x_122, 2);
x_128 = lean_array_get_size(x_101);
lean_dec_ref(x_101);
x_129 = lean_array_get_size(x_124);
lean_inc(x_129);
x_130 = l_Array_extract___redArg(x_124, x_128, x_129);
lean_inc(x_123);
x_131 = lean_apply_1(x_1, x_123);
x_132 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_2, x_131, x_130);
x_133 = l_Lake_BuildMetadata_writeFile(x_3, x_132, x_112);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_129);
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
x_136 = lean_box(0);
lean_inc(x_123);
if (lean_is_scalar(x_135)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_135;
 lean_ctor_set_tag(x_137, 1);
}
lean_ctor_set(x_137, 0, x_123);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_137);
x_139 = l_Lake_buildAction___redArg___lam__0(x_106, x_138, x_122, x_134);
lean_dec_ref(x_138);
lean_dec(x_106);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_142 = x_139;
} else {
 lean_dec_ref(x_139);
 x_142 = lean_box(0);
}
x_143 = lean_ctor_get(x_140, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_144 = x_140;
} else {
 lean_dec_ref(x_140);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_123);
lean_ctor_set(x_145, 1, x_143);
if (lean_is_scalar(x_142)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_142;
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_141);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_inc(x_127);
lean_inc_ref(x_126);
lean_inc_ref(x_124);
lean_dec(x_123);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 lean_ctor_release(x_122, 2);
 x_147 = x_122;
} else {
 lean_dec_ref(x_122);
 x_147 = lean_box(0);
}
x_148 = lean_ctor_get(x_133, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_133, 1);
lean_inc(x_149);
lean_dec_ref(x_133);
x_150 = lean_io_error_to_string(x_148);
x_151 = 3;
x_152 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set_uint8(x_152, sizeof(void*)*1, x_151);
x_153 = lean_array_push(x_124, x_152);
if (lean_is_scalar(x_147)) {
 x_154 = lean_alloc_ctor(0, 3, 1);
} else {
 x_154 = x_147;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_126);
lean_ctor_set(x_154, 2, x_127);
lean_ctor_set_uint8(x_154, sizeof(void*)*3, x_125);
x_113 = x_129;
x_114 = x_154;
x_115 = x_149;
goto block_121;
}
}
else
{
lean_object* x_155; lean_object* x_156; 
lean_dec_ref(x_101);
lean_dec_ref(x_1);
x_155 = lean_ctor_get(x_111, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_111, 1);
lean_inc(x_156);
lean_dec_ref(x_111);
x_113 = x_155;
x_114 = x_156;
x_115 = x_112;
goto block_121;
}
block_121:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_116 = lean_box(0);
x_117 = l_Lake_buildAction___redArg___lam__0(x_106, x_116, x_114, x_115);
lean_dec(x_106);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec_ref(x_117);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_13 = x_113;
x_14 = x_120;
x_15 = x_119;
goto block_18;
}
}
}
else
{
uint8_t x_157; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_157 = !lean_is_exclusive(x_11);
if (x_157 == 0)
{
lean_object* x_158; uint8_t x_159; uint8_t x_160; uint8_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_158 = lean_ctor_get(x_11, 0);
x_159 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_160 = 3;
x_161 = l_Lake_JobAction_merge(x_159, x_160);
x_162 = l_Lake_buildAction___redArg___closed__1;
x_163 = lean_array_get_size(x_158);
x_164 = lean_array_push(x_158, x_162);
lean_ctor_set(x_11, 0, x_164);
lean_ctor_set_uint8(x_11, sizeof(void*)*3, x_161);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_11);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_12);
return x_166;
}
else
{
lean_object* x_167; uint8_t x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_167 = lean_ctor_get(x_11, 0);
x_168 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_169 = lean_ctor_get(x_11, 1);
x_170 = lean_ctor_get(x_11, 2);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_167);
lean_dec(x_11);
x_171 = 3;
x_172 = l_Lake_JobAction_merge(x_168, x_171);
x_173 = l_Lake_buildAction___redArg___closed__1;
x_174 = lean_array_get_size(x_167);
x_175 = lean_array_push(x_167, x_173);
x_176 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_169);
lean_ctor_set(x_176, 2, x_170);
lean_ctor_set_uint8(x_176, sizeof(void*)*3, x_172);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_176);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_12);
return x_178;
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
LEAN_EXPORT lean_object* l_Lake_buildAction___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_buildAction___redArg___lam__0(x_1, x_2, x_3, x_4);
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
x_14 = l_Lake_buildAction___redArg(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
x_15 = l_Lake_buildAction(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_15;
}
}
static lean_object* _init_l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instToJsonPUnit__lake___lam__0), 1, 0);
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
lean_inc_ref(x_5);
x_18 = l_Lake_readTraceFile(x_5, x_17, x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
lean_ctor_set(x_14, 0, x_22);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
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
lean_dec_ref(x_23);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec_ref(x_24);
x_29 = l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0;
x_30 = l_Lake_buildAction___redArg(x_29, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_28, x_27);
lean_dec_ref(x_5);
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
lean_dec_ref(x_24);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
return x_23;
}
}
else
{
lean_dec_ref(x_24);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
return x_23;
}
}
else
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_55 = lean_ctor_get(x_14, 0);
x_56 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
x_57 = lean_ctor_get(x_14, 1);
x_58 = lean_ctor_get(x_14, 2);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_55);
lean_dec(x_14);
lean_inc_ref(x_5);
x_59 = l_Lake_readTraceFile(x_5, x_55, x_15);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec_ref(x_59);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_57);
lean_ctor_set(x_64, 2, x_58);
lean_ctor_set_uint8(x_64, sizeof(void*)*3, x_56);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_65 = l_Lake_SavedTrace_replayIfUpToDate___redArg(x_1, x_2, x_3, x_4, x_62, x_8, x_9, x_10, x_11, x_12, x_13, x_64, x_61);
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
lean_dec_ref(x_65);
x_70 = lean_ctor_get(x_66, 1);
lean_inc(x_70);
lean_dec_ref(x_66);
x_71 = l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0;
x_72 = l_Lake_buildAction___redArg(x_71, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_70, x_69);
lean_dec_ref(x_5);
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
lean_dec_ref(x_66);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
return x_65;
}
}
else
{
lean_dec_ref(x_66);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
return x_65;
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
lean_inc_ref(x_6);
x_19 = l_Lake_readTraceFile(x_6, x_18, x_16);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
lean_ctor_set(x_15, 0, x_23);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
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
lean_dec_ref(x_24);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec_ref(x_25);
x_30 = l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0;
x_31 = l_Lake_buildAction___redArg(x_30, x_5, x_6, x_7, x_8, x_10, x_11, x_12, x_13, x_14, x_29, x_28);
lean_dec_ref(x_6);
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
lean_dec_ref(x_25);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
return x_24;
}
}
else
{
lean_dec_ref(x_25);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
return x_24;
}
}
else
{
lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_56 = lean_ctor_get(x_15, 0);
x_57 = lean_ctor_get_uint8(x_15, sizeof(void*)*3);
x_58 = lean_ctor_get(x_15, 1);
x_59 = lean_ctor_get(x_15, 2);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_56);
lean_dec(x_15);
lean_inc_ref(x_6);
x_60 = l_Lake_readTraceFile(x_6, x_56, x_16);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec_ref(x_60);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_58);
lean_ctor_set(x_65, 2, x_59);
lean_ctor_set_uint8(x_65, sizeof(void*)*3, x_57);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_66 = l_Lake_SavedTrace_replayIfUpToDate___redArg(x_2, x_3, x_4, x_5, x_63, x_9, x_10, x_11, x_12, x_13, x_14, x_65, x_62);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_unbox(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_66, 1);
lean_inc(x_70);
lean_dec_ref(x_66);
x_71 = lean_ctor_get(x_67, 1);
lean_inc(x_71);
lean_dec_ref(x_67);
x_72 = l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0;
x_73 = l_Lake_buildAction___redArg(x_72, x_5, x_6, x_7, x_8, x_10, x_11, x_12, x_13, x_14, x_71, x_70);
lean_dec_ref(x_6);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
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
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_78 = x_74;
} else {
 lean_dec_ref(x_74);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_68);
lean_ctor_set(x_79, 1, x_77);
if (lean_is_scalar(x_76)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_76;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_75);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_68);
x_81 = lean_ctor_get(x_73, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_82 = x_73;
} else {
 lean_dec_ref(x_73);
 x_82 = lean_box(0);
}
x_83 = lean_ctor_get(x_74, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_74, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_85 = x_74;
} else {
 lean_dec_ref(x_74);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
if (lean_is_scalar(x_82)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_82;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_81);
return x_87;
}
}
else
{
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
return x_66;
}
}
else
{
lean_dec_ref(x_67);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
return x_66;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_7);
x_17 = l_Lake_buildUnlessUpToDate_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
x_18 = l_Lake_buildUnlessUpToDate_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_17, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
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
lean_inc_ref(x_5);
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
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
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
x_49 = lean_unbox(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec_ref(x_31);
x_50 = lean_ctor_get(x_32, 1);
lean_inc(x_50);
lean_dec_ref(x_32);
x_51 = l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0;
x_52 = l_Lake_buildAction___redArg(x_51, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_50, x_33);
lean_dec_ref(x_5);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec_ref(x_52);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec_ref(x_53);
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
lean_dec_ref(x_52);
x_57 = lean_ctor_get(x_53, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
lean_dec_ref(x_53);
x_16 = x_57;
x_17 = x_58;
x_18 = x_56;
goto block_21;
}
}
else
{
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_40 = x_31;
goto block_47;
}
}
else
{
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
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
lean_dec_ref(x_40);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec_ref(x_41);
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
lean_dec_ref(x_40);
x_45 = lean_ctor_get(x_41, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_dec_ref(x_41);
x_16 = x_45;
x_17 = x_46;
x_18 = x_44;
goto block_21;
}
}
}
else
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_80; 
x_59 = lean_ctor_get(x_14, 0);
x_60 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
x_61 = lean_ctor_get(x_14, 1);
x_62 = lean_ctor_get(x_14, 2);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_59);
lean_dec(x_14);
lean_inc_ref(x_5);
x_63 = l_Lake_readTraceFile(x_5, x_59, x_15);
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
x_70 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_61);
lean_ctor_set(x_70, 2, x_62);
lean_ctor_set_uint8(x_70, sizeof(void*)*3, x_60);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_71 = l_Lake_SavedTrace_replayIfUpToDate___redArg(x_1, x_2, x_3, x_4, x_67, x_8, x_9, x_10, x_11, x_12, x_13, x_70, x_65);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
x_74 = lean_box(0);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_72, 0);
x_89 = lean_unbox(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec_ref(x_71);
x_90 = lean_ctor_get(x_72, 1);
lean_inc(x_90);
lean_dec_ref(x_72);
x_91 = l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0;
x_92 = l_Lake_buildAction___redArg(x_91, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_90, x_73);
lean_dec_ref(x_5);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec_ref(x_92);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec_ref(x_93);
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
lean_dec_ref(x_92);
x_97 = lean_ctor_get(x_93, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_93, 1);
lean_inc(x_98);
lean_dec_ref(x_93);
x_16 = x_97;
x_17 = x_98;
x_18 = x_96;
goto block_21;
}
}
else
{
lean_dec(x_73);
lean_dec_ref(x_72);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_80 = x_71;
goto block_87;
}
}
else
{
lean_dec(x_73);
lean_dec_ref(x_72);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
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
lean_dec_ref(x_80);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec_ref(x_81);
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
lean_dec_ref(x_80);
x_85 = lean_ctor_get(x_81, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_81, 1);
lean_inc(x_86);
lean_dec_ref(x_81);
x_16 = x_85;
x_17 = x_86;
x_18 = x_84;
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
lean_inc_ref(x_6);
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
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
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
x_50 = lean_unbox(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec_ref(x_32);
x_51 = lean_ctor_get(x_33, 1);
lean_inc(x_51);
lean_dec_ref(x_33);
x_52 = l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0;
x_53 = l_Lake_buildAction___redArg(x_52, x_5, x_6, x_7, x_8, x_10, x_11, x_12, x_13, x_14, x_51, x_34);
lean_dec_ref(x_6);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec_ref(x_53);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec_ref(x_54);
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
lean_dec_ref(x_53);
x_58 = lean_ctor_get(x_54, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_dec_ref(x_54);
x_17 = x_58;
x_18 = x_59;
x_19 = x_57;
goto block_22;
}
}
else
{
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_41 = x_32;
goto block_48;
}
}
else
{
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
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
lean_dec_ref(x_41);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
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
lean_dec_ref(x_41);
x_46 = lean_ctor_get(x_42, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
lean_dec_ref(x_42);
x_17 = x_46;
x_18 = x_47;
x_19 = x_45;
goto block_22;
}
}
}
else
{
lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_81; 
x_60 = lean_ctor_get(x_15, 0);
x_61 = lean_ctor_get_uint8(x_15, sizeof(void*)*3);
x_62 = lean_ctor_get(x_15, 1);
x_63 = lean_ctor_get(x_15, 2);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_60);
lean_dec(x_15);
lean_inc_ref(x_6);
x_64 = l_Lake_readTraceFile(x_6, x_60, x_16);
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
x_68 = lean_ctor_get(x_65, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_70 = x_65;
} else {
 lean_dec_ref(x_65);
 x_70 = lean_box(0);
}
x_71 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_62);
lean_ctor_set(x_71, 2, x_63);
lean_ctor_set_uint8(x_71, sizeof(void*)*3, x_61);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_72 = l_Lake_SavedTrace_replayIfUpToDate___redArg(x_2, x_3, x_4, x_5, x_68, x_9, x_10, x_11, x_12, x_13, x_14, x_71, x_66);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
x_75 = lean_box(0);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_73, 0);
x_90 = lean_unbox(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec_ref(x_72);
x_91 = lean_ctor_get(x_73, 1);
lean_inc(x_91);
lean_dec_ref(x_73);
x_92 = l_Lake_buildUnlessUpToDate_x3f___redArg___closed__0;
x_93 = l_Lake_buildAction___redArg(x_92, x_5, x_6, x_7, x_8, x_10, x_11, x_12, x_13, x_14, x_91, x_74);
lean_dec_ref(x_6);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec_ref(x_93);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec_ref(x_94);
x_76 = x_96;
x_77 = x_95;
goto block_80;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_70);
lean_dec(x_67);
x_97 = lean_ctor_get(x_93, 1);
lean_inc(x_97);
lean_dec_ref(x_93);
x_98 = lean_ctor_get(x_94, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_94, 1);
lean_inc(x_99);
lean_dec_ref(x_94);
x_17 = x_98;
x_18 = x_99;
x_19 = x_97;
goto block_22;
}
}
else
{
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_81 = x_72;
goto block_88;
}
}
else
{
lean_dec(x_74);
lean_dec_ref(x_73);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
x_81 = x_72;
goto block_88;
}
block_80:
{
lean_object* x_78; lean_object* x_79; 
if (lean_is_scalar(x_70)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_70;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
if (lean_is_scalar(x_67)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_67;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
block_88:
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec_ref(x_81);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec_ref(x_82);
x_76 = x_84;
x_77 = x_83;
goto block_80;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_70);
lean_dec(x_67);
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
lean_dec_ref(x_81);
x_86 = lean_ctor_get(x_82, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_82, 1);
lean_inc(x_87);
lean_dec_ref(x_82);
x_17 = x_86;
x_18 = x_87;
x_19 = x_85;
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
x_17 = l_Lake_buildUnlessUpToDate___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
x_18 = l_Lake_buildUnlessUpToDate(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_17, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
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
lean_dec_ref(x_6);
x_8 = lean_uint64_to_nat(x_2);
x_9 = l_Nat_reprFast(x_8);
x_10 = l_IO_FS_writeFile(x_5, x_9, x_7);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
return x_10;
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
lean_dec_ref(x_4);
x_7 = lean_unbox_uint64(x_5);
lean_dec(x_5);
x_8 = l_Lake_writeFileHash(x_1, x_7, x_6);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec_ref(x_1);
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
lean_dec_ref(x_4);
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
lean_dec_ref(x_6);
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
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_89; lean_object* x_90; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 1);
x_8 = l_Lake_writeFileHash___closed__0;
lean_inc_ref(x_1);
x_9 = lean_string_append(x_1, x_8);
if (x_7 == 0)
{
x_89 = x_4;
x_90 = x_5;
goto block_101;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = l_Lake_Hash_load_x3f(x_9, x_5);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec_ref(x_102);
x_89 = x_4;
x_90 = x_104;
goto block_101;
}
else
{
uint8_t x_105; 
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_105 = !lean_is_exclusive(x_102);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_102, 0);
lean_dec(x_106);
x_107 = lean_ctor_get(x_103, 0);
lean_inc(x_107);
lean_dec_ref(x_103);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_4);
lean_ctor_set(x_102, 0, x_108);
return x_102;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_102, 1);
lean_inc(x_109);
lean_dec(x_102);
x_110 = lean_ctor_get(x_103, 0);
lean_inc(x_110);
lean_dec_ref(x_103);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_4);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_109);
return x_112;
}
}
}
block_88:
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = l_Lake_createParentDirs(x_9, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint64_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_unbox_uint64(x_15);
x_20 = lean_uint64_to_nat(x_19);
x_21 = l_Nat_reprFast(x_20);
x_22 = l_IO_FS_writeFile(x_9, x_21, x_18);
lean_dec_ref(x_21);
lean_dec_ref(x_9);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_25, 0, x_10);
lean_ctor_set(x_25, 1, x_13);
lean_ctor_set(x_25, 2, x_12);
lean_ctor_set_uint8(x_25, sizeof(void*)*3, x_11);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_15);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_28, 0, x_10);
lean_ctor_set(x_28, 1, x_13);
lean_ctor_set(x_28, 2, x_12);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_11);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_15);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_15);
x_31 = !lean_is_exclusive(x_22);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_22, 0);
x_33 = lean_io_error_to_string(x_32);
x_34 = 3;
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
x_36 = lean_array_get_size(x_10);
x_37 = lean_array_push(x_10, x_35);
x_38 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_13);
lean_ctor_set(x_38, 2, x_12);
lean_ctor_set_uint8(x_38, sizeof(void*)*3, x_11);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set_tag(x_22, 0);
lean_ctor_set(x_22, 0, x_39);
return x_22;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_40 = lean_ctor_get(x_22, 0);
x_41 = lean_ctor_get(x_22, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_22);
x_42 = lean_io_error_to_string(x_40);
x_43 = 3;
x_44 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_43);
x_45 = lean_array_get_size(x_10);
x_46 = lean_array_push(x_10, x_44);
x_47 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_13);
lean_ctor_set(x_47, 2, x_12);
lean_ctor_set_uint8(x_47, sizeof(void*)*3, x_11);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_41);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_15);
lean_dec_ref(x_9);
x_50 = !lean_is_exclusive(x_17);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_51 = lean_ctor_get(x_17, 0);
x_52 = lean_io_error_to_string(x_51);
x_53 = 3;
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_53);
x_55 = lean_array_get_size(x_10);
x_56 = lean_array_push(x_10, x_54);
x_57 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_13);
lean_ctor_set(x_57, 2, x_12);
lean_ctor_set_uint8(x_57, sizeof(void*)*3, x_11);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set_tag(x_17, 0);
lean_ctor_set(x_17, 0, x_58);
return x_17;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_59 = lean_ctor_get(x_17, 0);
x_60 = lean_ctor_get(x_17, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_17);
x_61 = lean_io_error_to_string(x_59);
x_62 = 3;
x_63 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_62);
x_64 = lean_array_get_size(x_10);
x_65 = lean_array_push(x_10, x_63);
x_66 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_13);
lean_ctor_set(x_66, 2, x_12);
lean_ctor_set_uint8(x_66, sizeof(void*)*3, x_11);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_60);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec_ref(x_9);
x_69 = !lean_is_exclusive(x_14);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_70 = lean_ctor_get(x_14, 0);
x_71 = lean_io_error_to_string(x_70);
x_72 = 3;
x_73 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set_uint8(x_73, sizeof(void*)*1, x_72);
x_74 = lean_array_get_size(x_10);
x_75 = lean_array_push(x_10, x_73);
x_76 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_13);
lean_ctor_set(x_76, 2, x_12);
lean_ctor_set_uint8(x_76, sizeof(void*)*3, x_11);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 0, x_77);
return x_14;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_78 = lean_ctor_get(x_14, 0);
x_79 = lean_ctor_get(x_14, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_14);
x_80 = lean_io_error_to_string(x_78);
x_81 = 3;
x_82 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set_uint8(x_82, sizeof(void*)*1, x_81);
x_83 = lean_array_get_size(x_10);
x_84 = lean_array_push(x_10, x_82);
x_85 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_13);
lean_ctor_set(x_85, 2, x_12);
lean_ctor_set_uint8(x_85, sizeof(void*)*3, x_11);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_79);
return x_87;
}
}
}
block_101:
{
if (x_2 == 0)
{
lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_ctor_get(x_89, 0);
lean_inc_ref(x_91);
x_92 = lean_ctor_get_uint8(x_89, sizeof(void*)*3);
x_93 = lean_ctor_get(x_89, 1);
lean_inc_ref(x_93);
x_94 = lean_ctor_get(x_89, 2);
lean_inc(x_94);
lean_dec_ref(x_89);
x_95 = l_Lake_computeBinFileHash(x_1, x_90);
lean_dec_ref(x_1);
x_10 = x_91;
x_11 = x_92;
x_12 = x_94;
x_13 = x_93;
x_14 = x_95;
goto block_88;
}
else
{
lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_ctor_get(x_89, 0);
lean_inc_ref(x_96);
x_97 = lean_ctor_get_uint8(x_89, sizeof(void*)*3);
x_98 = lean_ctor_get(x_89, 1);
lean_inc_ref(x_98);
x_99 = lean_ctor_get(x_89, 2);
lean_inc(x_99);
lean_dec_ref(x_89);
x_100 = l_Lake_computeTextFileHash(x_1, x_90);
lean_dec_ref(x_1);
x_10 = x_96;
x_11 = x_97;
x_12 = x_99;
x_13 = x_98;
x_14 = x_100;
goto block_88;
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
x_7 = l_Lake_fetchFileHash___redArg(x_1, x_6, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_Lake_fetchFileHash(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc_ref(x_1);
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
lean_dec_ref(x_6);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_15 = lean_ctor_get(x_8, 1);
x_16 = lean_ctor_get(x_8, 2);
x_17 = lean_io_metadata(x_1, x_9);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_20);
lean_dec(x_19);
x_21 = l_Lake_platformTrace___closed__4;
x_22 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_20);
x_23 = lean_unbox_uint64(x_11);
lean_dec(x_11);
lean_ctor_set_uint64(x_22, sizeof(void*)*3, x_23);
lean_ctor_set(x_7, 0, x_22);
lean_ctor_set(x_17, 0, x_7);
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_26);
lean_dec(x_24);
x_27 = l_Lake_platformTrace___closed__4;
x_28 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_26);
x_29 = lean_unbox_uint64(x_11);
lean_dec(x_11);
lean_ctor_set_uint64(x_28, sizeof(void*)*3, x_29);
lean_ctor_set(x_7, 0, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_7);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc_ref(x_13);
lean_dec(x_11);
lean_dec_ref(x_1);
x_31 = !lean_is_exclusive(x_8);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_8, 2);
lean_dec(x_32);
x_33 = lean_ctor_get(x_8, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_8, 0);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_17);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_17, 0);
x_37 = lean_io_error_to_string(x_36);
x_38 = 3;
x_39 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_38);
x_40 = lean_array_get_size(x_13);
x_41 = lean_array_push(x_13, x_39);
lean_ctor_set(x_8, 0, x_41);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_40);
lean_ctor_set_tag(x_17, 0);
lean_ctor_set(x_17, 0, x_7);
return x_17;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_17, 0);
x_43 = lean_ctor_get(x_17, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_17);
x_44 = lean_io_error_to_string(x_42);
x_45 = 3;
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_45);
x_47 = lean_array_get_size(x_13);
x_48 = lean_array_push(x_13, x_46);
lean_ctor_set(x_8, 0, x_48);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_7);
lean_ctor_set(x_49, 1, x_43);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_8);
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
x_53 = lean_io_error_to_string(x_50);
x_54 = 3;
x_55 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_54);
x_56 = lean_array_get_size(x_13);
x_57 = lean_array_push(x_13, x_55);
x_58 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_15);
lean_ctor_set(x_58, 2, x_16);
lean_ctor_set_uint8(x_58, sizeof(void*)*3, x_14);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_58);
lean_ctor_set(x_7, 0, x_56);
if (lean_is_scalar(x_52)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_52;
 lean_ctor_set_tag(x_59, 0);
}
lean_ctor_set(x_59, 0, x_7);
lean_ctor_set(x_59, 1, x_51);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_7, 0);
lean_inc(x_60);
lean_dec(x_7);
x_61 = lean_ctor_get(x_8, 0);
x_62 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_63 = lean_ctor_get(x_8, 1);
x_64 = lean_ctor_get(x_8, 2);
x_65 = lean_io_metadata(x_1, x_9);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint64_t x_72; lean_object* x_73; lean_object* x_74; 
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
x_69 = lean_ctor_get(x_66, 1);
lean_inc_ref(x_69);
lean_dec(x_66);
x_70 = l_Lake_platformTrace___closed__4;
x_71 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_71, 0, x_1);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_71, 2, x_69);
x_72 = lean_unbox_uint64(x_60);
lean_dec(x_60);
lean_ctor_set_uint64(x_71, sizeof(void*)*3, x_72);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_8);
if (lean_is_scalar(x_68)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_68;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_67);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_inc(x_64);
lean_inc_ref(x_63);
lean_inc_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 x_75 = x_8;
} else {
 lean_dec_ref(x_8);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get(x_65, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_65, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_78 = x_65;
} else {
 lean_dec_ref(x_65);
 x_78 = lean_box(0);
}
x_79 = lean_io_error_to_string(x_76);
x_80 = 3;
x_81 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set_uint8(x_81, sizeof(void*)*1, x_80);
x_82 = lean_array_get_size(x_61);
x_83 = lean_array_push(x_61, x_81);
if (lean_is_scalar(x_75)) {
 x_84 = lean_alloc_ctor(0, 3, 1);
} else {
 x_84 = x_75;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_63);
lean_ctor_set(x_84, 2, x_64);
lean_ctor_set_uint8(x_84, sizeof(void*)*3, x_62);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_84);
if (lean_is_scalar(x_78)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_78;
 lean_ctor_set_tag(x_86, 0);
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_77);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec_ref(x_1);
x_87 = !lean_is_exclusive(x_6);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_6, 0);
lean_dec(x_88);
x_89 = !lean_is_exclusive(x_7);
if (x_89 == 0)
{
return x_6;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_7, 0);
x_91 = lean_ctor_get(x_7, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_7);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set(x_6, 0, x_92);
return x_6;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_6, 1);
lean_inc(x_93);
lean_dec(x_6);
x_94 = lean_ctor_get(x_7, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_7, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_96 = x_7;
} else {
 lean_dec_ref(x_7);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_93);
return x_98;
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
x_7 = l_Lake_fetchFileTrace___redArg(x_1, x_6, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_Lake_fetchFileTrace(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
LEAN_EXPORT uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_2, 2);
x_23 = l_Lake_MTime_checkUpToDate___at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(x_1, x_22, x_7);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_6);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_6);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
case 1:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_40; uint8_t x_41; 
x_31 = l_Lake_MTime_checkUpToDate___at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(x_1, x_4, x_7);
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
x_40 = lean_ctor_get(x_5, 0);
x_41 = lean_ctor_get_uint8(x_40, sizeof(void*)*1);
if (x_41 == 0)
{
lean_dec(x_32);
x_35 = x_41;
goto block_39;
}
else
{
uint8_t x_42; 
x_42 = lean_unbox(x_32);
lean_dec(x_32);
x_35 = x_42;
goto block_39;
}
block_39:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_box(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_6);
if (lean_is_scalar(x_34)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_34;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
}
default: 
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_3);
if (x_43 == 0)
{
lean_object* x_44; uint64_t x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; uint64_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_44 = lean_ctor_get(x_3, 0);
x_45 = lean_ctor_get_uint64(x_44, sizeof(void*)*3);
x_46 = lean_ctor_get(x_44, 2);
lean_inc_ref(x_46);
lean_dec_ref(x_44);
x_84 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
x_85 = lean_box_uint64(x_45);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_85);
x_86 = lean_box_uint64(x_84);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
x_88 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(x_87, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_87);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_5, 0);
x_90 = lean_ctor_get_uint8(x_89, sizeof(void*)*1);
if (x_90 == 0)
{
lean_dec_ref(x_46);
x_8 = x_90;
x_9 = x_6;
x_10 = x_7;
goto block_14;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_91 = l_Lake_MTime_checkUpToDate___at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(x_1, x_4, x_7);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec_ref(x_91);
x_94 = lean_unbox(x_92);
lean_dec(x_92);
x_47 = x_94;
x_48 = x_6;
x_49 = x_93;
goto block_83;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_95 = l_System_FilePath_pathExists(x_1, x_7);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec_ref(x_95);
x_98 = lean_unbox(x_96);
lean_dec(x_96);
x_47 = x_98;
x_48 = x_6;
x_49 = x_97;
goto block_83;
}
block_83:
{
if (x_47 == 0)
{
lean_dec_ref(x_46);
x_8 = x_47;
x_9 = x_48;
x_10 = x_49;
goto block_14;
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_48);
if (x_50 == 0)
{
uint8_t x_51; uint8_t x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_51 = lean_ctor_get_uint8(x_48, sizeof(void*)*3);
x_52 = 1;
x_53 = l_Lake_JobAction_merge(x_51, x_52);
lean_ctor_set_uint8(x_48, sizeof(void*)*3, x_53);
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_array_get_size(x_46);
x_56 = lean_nat_dec_lt(x_54, x_55);
if (x_56 == 0)
{
lean_dec(x_55);
lean_dec_ref(x_46);
x_15 = x_47;
x_16 = x_48;
x_17 = x_49;
goto block_21;
}
else
{
uint8_t x_57; 
x_57 = lean_nat_dec_le(x_55, x_55);
if (x_57 == 0)
{
lean_dec(x_55);
lean_dec_ref(x_46);
x_15 = x_47;
x_16 = x_48;
x_17 = x_49;
goto block_21;
}
else
{
lean_object* x_58; size_t x_59; size_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_58 = lean_box(0);
x_59 = 0;
x_60 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_61 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayOrFetch_spec__0___redArg(x_46, x_59, x_60, x_58, x_48, x_49);
lean_dec_ref(x_46);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec_ref(x_61);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_15 = x_47;
x_16 = x_64;
x_17 = x_63;
goto block_21;
}
}
}
else
{
lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_65 = lean_ctor_get(x_48, 0);
x_66 = lean_ctor_get_uint8(x_48, sizeof(void*)*3);
x_67 = lean_ctor_get(x_48, 1);
x_68 = lean_ctor_get(x_48, 2);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_65);
lean_dec(x_48);
x_69 = 1;
x_70 = l_Lake_JobAction_merge(x_66, x_69);
x_71 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_71, 0, x_65);
lean_ctor_set(x_71, 1, x_67);
lean_ctor_set(x_71, 2, x_68);
lean_ctor_set_uint8(x_71, sizeof(void*)*3, x_70);
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_array_get_size(x_46);
x_74 = lean_nat_dec_lt(x_72, x_73);
if (x_74 == 0)
{
lean_dec(x_73);
lean_dec_ref(x_46);
x_15 = x_47;
x_16 = x_71;
x_17 = x_49;
goto block_21;
}
else
{
uint8_t x_75; 
x_75 = lean_nat_dec_le(x_73, x_73);
if (x_75 == 0)
{
lean_dec(x_73);
lean_dec_ref(x_46);
x_15 = x_47;
x_16 = x_71;
x_17 = x_49;
goto block_21;
}
else
{
lean_object* x_76; size_t x_77; size_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_76 = lean_box(0);
x_77 = 0;
x_78 = lean_usize_of_nat(x_73);
lean_dec(x_73);
x_79 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayOrFetch_spec__0___redArg(x_46, x_77, x_78, x_76, x_71, x_49);
lean_dec_ref(x_46);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec_ref(x_79);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_15 = x_47;
x_16 = x_82;
x_17 = x_81;
goto block_21;
}
}
}
}
}
}
else
{
lean_object* x_99; uint64_t x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; uint64_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_99 = lean_ctor_get(x_3, 0);
lean_inc(x_99);
lean_dec(x_3);
x_100 = lean_ctor_get_uint64(x_99, sizeof(void*)*3);
x_101 = lean_ctor_get(x_99, 2);
lean_inc_ref(x_101);
lean_dec_ref(x_99);
x_125 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
x_126 = lean_box_uint64(x_100);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
x_128 = lean_box_uint64(x_125);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_128);
x_130 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(x_129, x_127);
lean_dec_ref(x_127);
lean_dec_ref(x_129);
if (x_130 == 0)
{
lean_object* x_131; uint8_t x_132; 
x_131 = lean_ctor_get(x_5, 0);
x_132 = lean_ctor_get_uint8(x_131, sizeof(void*)*1);
if (x_132 == 0)
{
lean_dec_ref(x_101);
x_8 = x_132;
x_9 = x_6;
x_10 = x_7;
goto block_14;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_133 = l_Lake_MTime_checkUpToDate___at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(x_1, x_4, x_7);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec_ref(x_133);
x_136 = lean_unbox(x_134);
lean_dec(x_134);
x_102 = x_136;
x_103 = x_6;
x_104 = x_135;
goto block_124;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_137 = l_System_FilePath_pathExists(x_1, x_7);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec_ref(x_137);
x_140 = lean_unbox(x_138);
lean_dec(x_138);
x_102 = x_140;
x_103 = x_6;
x_104 = x_139;
goto block_124;
}
block_124:
{
if (x_102 == 0)
{
lean_dec_ref(x_101);
x_8 = x_102;
x_9 = x_103;
x_10 = x_104;
goto block_14;
}
else
{
lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_105 = lean_ctor_get(x_103, 0);
lean_inc_ref(x_105);
x_106 = lean_ctor_get_uint8(x_103, sizeof(void*)*3);
x_107 = lean_ctor_get(x_103, 1);
lean_inc_ref(x_107);
x_108 = lean_ctor_get(x_103, 2);
lean_inc(x_108);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 lean_ctor_release(x_103, 2);
 x_109 = x_103;
} else {
 lean_dec_ref(x_103);
 x_109 = lean_box(0);
}
x_110 = 1;
x_111 = l_Lake_JobAction_merge(x_106, x_110);
if (lean_is_scalar(x_109)) {
 x_112 = lean_alloc_ctor(0, 3, 1);
} else {
 x_112 = x_109;
}
lean_ctor_set(x_112, 0, x_105);
lean_ctor_set(x_112, 1, x_107);
lean_ctor_set(x_112, 2, x_108);
lean_ctor_set_uint8(x_112, sizeof(void*)*3, x_111);
x_113 = lean_unsigned_to_nat(0u);
x_114 = lean_array_get_size(x_101);
x_115 = lean_nat_dec_lt(x_113, x_114);
if (x_115 == 0)
{
lean_dec(x_114);
lean_dec_ref(x_101);
x_15 = x_102;
x_16 = x_112;
x_17 = x_104;
goto block_21;
}
else
{
uint8_t x_116; 
x_116 = lean_nat_dec_le(x_114, x_114);
if (x_116 == 0)
{
lean_dec(x_114);
lean_dec_ref(x_101);
x_15 = x_102;
x_16 = x_112;
x_17 = x_104;
goto block_21;
}
else
{
lean_object* x_117; size_t x_118; size_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_117 = lean_box(0);
x_118 = 0;
x_119 = lean_usize_of_nat(x_114);
lean_dec(x_114);
x_120 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_SavedTrace_replayOrFetch_spec__0___redArg(x_101, x_118, x_119, x_117, x_112, x_104);
lean_dec_ref(x_101);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec_ref(x_120);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_15 = x_102;
x_16 = x_123;
x_17 = x_122;
goto block_21;
}
}
}
}
}
}
}
block_14:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_box(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
block_21:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_box(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0___redArg(x_2, x_3, x_4, x_5, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__3___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get_uint8(x_19, sizeof(void*)*1 + 2);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_24 = lean_io_mono_ms_now(x_12);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = l_Lake_JobAction_merge(x_23, x_6);
lean_inc_ref(x_22);
lean_ctor_set_uint8(x_11, sizeof(void*)*3, x_27);
x_28 = lean_apply_7(x_1, x_3, x_7, x_8, x_9, x_10, x_11, x_26);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec_ref(x_28);
x_91 = lean_ctor_get(x_29, 1);
lean_inc(x_91);
lean_dec_ref(x_29);
x_92 = lean_ctor_get(x_91, 0);
lean_inc_ref(x_92);
x_93 = lean_ctor_get_uint8(x_91, sizeof(void*)*3);
x_94 = lean_ctor_get(x_91, 1);
lean_inc_ref(x_94);
x_95 = lean_ctor_get(x_91, 2);
lean_inc(x_95);
x_96 = l_Lake_clearFileHash(x_2, x_30);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec_ref(x_96);
x_40 = x_97;
x_41 = x_91;
x_42 = x_92;
x_43 = x_93;
x_44 = x_94;
x_45 = x_95;
x_46 = x_98;
goto block_90;
}
else
{
uint8_t x_99; 
lean_dec_ref(x_22);
x_99 = !lean_is_exclusive(x_91);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_100 = lean_ctor_get(x_91, 2);
lean_dec(x_100);
x_101 = lean_ctor_get(x_91, 1);
lean_dec(x_101);
x_102 = lean_ctor_get(x_91, 0);
lean_dec(x_102);
x_103 = lean_ctor_get(x_96, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_96, 1);
lean_inc(x_104);
lean_dec_ref(x_96);
x_105 = lean_io_error_to_string(x_103);
x_106 = 3;
x_107 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set_uint8(x_107, sizeof(void*)*1, x_106);
x_108 = lean_array_get_size(x_92);
x_109 = lean_array_push(x_92, x_107);
lean_ctor_set(x_91, 0, x_109);
x_31 = x_108;
x_32 = x_91;
x_33 = x_104;
goto block_39;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_91);
x_110 = lean_ctor_get(x_96, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_96, 1);
lean_inc(x_111);
lean_dec_ref(x_96);
x_112 = lean_io_error_to_string(x_110);
x_113 = 3;
x_114 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set_uint8(x_114, sizeof(void*)*1, x_113);
x_115 = lean_array_get_size(x_92);
x_116 = lean_array_push(x_92, x_114);
x_117 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_94);
lean_ctor_set(x_117, 2, x_95);
lean_ctor_set_uint8(x_117, sizeof(void*)*3, x_93);
x_31 = x_115;
x_32 = x_117;
x_33 = x_111;
goto block_39;
}
}
}
else
{
lean_object* x_118; 
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_2);
x_118 = lean_ctor_get(x_28, 0);
lean_inc(x_118);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; 
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_28, 1);
lean_inc(x_120);
lean_dec_ref(x_28);
x_121 = lean_ctor_get(x_118, 0);
lean_inc(x_121);
lean_dec_ref(x_118);
x_122 = lean_ctor_get(x_119, 0);
lean_inc_ref(x_122);
x_123 = lean_ctor_get_uint8(x_119, sizeof(void*)*3);
x_124 = lean_ctor_get(x_119, 1);
lean_inc_ref(x_124);
x_125 = lean_ctor_get(x_119, 2);
lean_inc(x_125);
x_40 = x_121;
x_41 = x_119;
x_42 = x_122;
x_43 = x_123;
x_44 = x_124;
x_45 = x_125;
x_46 = x_120;
goto block_90;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec_ref(x_22);
x_126 = lean_ctor_get(x_28, 1);
lean_inc(x_126);
lean_dec_ref(x_28);
x_127 = lean_ctor_get(x_118, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_118, 1);
lean_inc(x_128);
lean_dec_ref(x_118);
x_31 = x_127;
x_32 = x_128;
x_33 = x_126;
goto block_39;
}
}
block_39:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_box(0);
x_35 = l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__3___lam__0(x_25, x_34, x_32, x_33);
lean_dec(x_25);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_13 = x_31;
x_14 = x_38;
x_15 = x_37;
goto block_18;
}
block_90:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_array_get_size(x_22);
lean_dec_ref(x_22);
x_48 = lean_array_get_size(x_42);
lean_inc(x_48);
x_49 = l_Array_extract___redArg(x_42, x_47, x_48);
x_50 = lean_box(0);
x_51 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_4, x_50, x_49);
x_52 = l_Lake_BuildMetadata_writeFile(x_5, x_51, x_46);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
lean_dec(x_48);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec_ref(x_42);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_54 = lean_ctor_get(x_52, 1);
x_55 = lean_ctor_get(x_52, 0);
lean_dec(x_55);
x_56 = lean_box(0);
lean_ctor_set_tag(x_52, 1);
lean_ctor_set(x_52, 1, x_56);
lean_ctor_set(x_52, 0, x_40);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_52);
x_58 = l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__3___lam__0(x_25, x_57, x_41, x_54);
lean_dec_ref(x_57);
lean_dec(x_25);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_60, 0);
lean_dec(x_62);
lean_ctor_set(x_60, 0, x_40);
return x_58;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_40);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_58, 0, x_64);
return x_58;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_58, 0);
x_66 = lean_ctor_get(x_58, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_58);
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
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_40);
lean_ctor_set(x_69, 1, x_67);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_66);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_71 = lean_ctor_get(x_52, 1);
lean_inc(x_71);
lean_dec(x_52);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_40);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__3___lam__0(x_25, x_74, x_41, x_71);
lean_dec_ref(x_74);
lean_dec(x_25);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_78 = x_75;
} else {
 lean_dec_ref(x_75);
 x_78 = lean_box(0);
}
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_80 = x_76;
} else {
 lean_dec_ref(x_76);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_40);
lean_ctor_set(x_81, 1, x_79);
if (lean_is_scalar(x_78)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_78;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_77);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec_ref(x_41);
x_83 = lean_ctor_get(x_52, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_52, 1);
lean_inc(x_84);
lean_dec_ref(x_52);
x_85 = lean_io_error_to_string(x_83);
x_86 = 3;
x_87 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set_uint8(x_87, sizeof(void*)*1, x_86);
x_88 = lean_array_push(x_42, x_87);
x_89 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_44);
lean_ctor_set(x_89, 2, x_45);
lean_ctor_set_uint8(x_89, sizeof(void*)*3, x_43);
x_31 = x_48;
x_32 = x_89;
x_33 = x_84;
goto block_39;
}
}
}
else
{
lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_129 = lean_ctor_get(x_11, 0);
x_130 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_131 = lean_ctor_get(x_11, 1);
x_132 = lean_ctor_get(x_11, 2);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_129);
lean_dec(x_11);
x_133 = lean_io_mono_ms_now(x_12);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec_ref(x_133);
x_136 = l_Lake_JobAction_merge(x_130, x_6);
lean_inc_ref(x_129);
x_137 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_137, 0, x_129);
lean_ctor_set(x_137, 1, x_131);
lean_ctor_set(x_137, 2, x_132);
lean_ctor_set_uint8(x_137, sizeof(void*)*3, x_136);
x_138 = lean_apply_7(x_1, x_3, x_7, x_8, x_9, x_10, x_137, x_135);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec_ref(x_138);
x_184 = lean_ctor_get(x_139, 1);
lean_inc(x_184);
lean_dec_ref(x_139);
x_185 = lean_ctor_get(x_184, 0);
lean_inc_ref(x_185);
x_186 = lean_ctor_get_uint8(x_184, sizeof(void*)*3);
x_187 = lean_ctor_get(x_184, 1);
lean_inc_ref(x_187);
x_188 = lean_ctor_get(x_184, 2);
lean_inc(x_188);
x_189 = l_Lake_clearFileHash(x_2, x_140);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec_ref(x_189);
x_150 = x_190;
x_151 = x_184;
x_152 = x_185;
x_153 = x_186;
x_154 = x_187;
x_155 = x_188;
x_156 = x_191;
goto block_183;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec_ref(x_129);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 lean_ctor_release(x_184, 2);
 x_192 = x_184;
} else {
 lean_dec_ref(x_184);
 x_192 = lean_box(0);
}
x_193 = lean_ctor_get(x_189, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_189, 1);
lean_inc(x_194);
lean_dec_ref(x_189);
x_195 = lean_io_error_to_string(x_193);
x_196 = 3;
x_197 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set_uint8(x_197, sizeof(void*)*1, x_196);
x_198 = lean_array_get_size(x_185);
x_199 = lean_array_push(x_185, x_197);
if (lean_is_scalar(x_192)) {
 x_200 = lean_alloc_ctor(0, 3, 1);
} else {
 x_200 = x_192;
}
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_187);
lean_ctor_set(x_200, 2, x_188);
lean_ctor_set_uint8(x_200, sizeof(void*)*3, x_186);
x_141 = x_198;
x_142 = x_200;
x_143 = x_194;
goto block_149;
}
}
else
{
lean_object* x_201; 
lean_dec(x_140);
lean_dec_ref(x_139);
lean_dec_ref(x_2);
x_201 = lean_ctor_get(x_138, 0);
lean_inc(x_201);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; lean_object* x_207; lean_object* x_208; 
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
x_203 = lean_ctor_get(x_138, 1);
lean_inc(x_203);
lean_dec_ref(x_138);
x_204 = lean_ctor_get(x_201, 0);
lean_inc(x_204);
lean_dec_ref(x_201);
x_205 = lean_ctor_get(x_202, 0);
lean_inc_ref(x_205);
x_206 = lean_ctor_get_uint8(x_202, sizeof(void*)*3);
x_207 = lean_ctor_get(x_202, 1);
lean_inc_ref(x_207);
x_208 = lean_ctor_get(x_202, 2);
lean_inc(x_208);
x_150 = x_204;
x_151 = x_202;
x_152 = x_205;
x_153 = x_206;
x_154 = x_207;
x_155 = x_208;
x_156 = x_203;
goto block_183;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec_ref(x_129);
x_209 = lean_ctor_get(x_138, 1);
lean_inc(x_209);
lean_dec_ref(x_138);
x_210 = lean_ctor_get(x_201, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_201, 1);
lean_inc(x_211);
lean_dec_ref(x_201);
x_141 = x_210;
x_142 = x_211;
x_143 = x_209;
goto block_149;
}
}
block_149:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_144 = lean_box(0);
x_145 = l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__3___lam__0(x_134, x_144, x_142, x_143);
lean_dec(x_134);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec_ref(x_145);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_13 = x_141;
x_14 = x_148;
x_15 = x_147;
goto block_18;
}
block_183:
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_157 = lean_array_get_size(x_129);
lean_dec_ref(x_129);
x_158 = lean_array_get_size(x_152);
lean_inc(x_158);
x_159 = l_Array_extract___redArg(x_152, x_157, x_158);
x_160 = lean_box(0);
x_161 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_4, x_160, x_159);
x_162 = l_Lake_BuildMetadata_writeFile(x_5, x_161, x_156);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_158);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_152);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_164 = x_162;
} else {
 lean_dec_ref(x_162);
 x_164 = lean_box(0);
}
x_165 = lean_box(0);
if (lean_is_scalar(x_164)) {
 x_166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_166 = x_164;
 lean_ctor_set_tag(x_166, 1);
}
lean_ctor_set(x_166, 0, x_150);
lean_ctor_set(x_166, 1, x_165);
x_167 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_167, 0, x_166);
x_168 = l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__3___lam__0(x_134, x_167, x_151, x_163);
lean_dec_ref(x_167);
lean_dec(x_134);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_171 = x_168;
} else {
 lean_dec_ref(x_168);
 x_171 = lean_box(0);
}
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
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_150);
lean_ctor_set(x_174, 1, x_172);
if (lean_is_scalar(x_171)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_171;
}
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_170);
return x_175;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec_ref(x_151);
x_176 = lean_ctor_get(x_162, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_162, 1);
lean_inc(x_177);
lean_dec_ref(x_162);
x_178 = lean_io_error_to_string(x_176);
x_179 = 3;
x_180 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set_uint8(x_180, sizeof(void*)*1, x_179);
x_181 = lean_array_push(x_152, x_180);
x_182 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_154);
lean_ctor_set(x_182, 2, x_155);
lean_ctor_set_uint8(x_182, sizeof(void*)*3, x_153);
x_141 = x_158;
x_142 = x_182;
x_143 = x_177;
goto block_149;
}
}
}
}
else
{
uint8_t x_212; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_212 = !lean_is_exclusive(x_11);
if (x_212 == 0)
{
lean_object* x_213; uint8_t x_214; uint8_t x_215; uint8_t x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_213 = lean_ctor_get(x_11, 0);
x_214 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_215 = 3;
x_216 = l_Lake_JobAction_merge(x_214, x_215);
x_217 = l_Lake_buildAction___redArg___closed__1;
x_218 = lean_array_get_size(x_213);
x_219 = lean_array_push(x_213, x_217);
lean_ctor_set(x_11, 0, x_219);
lean_ctor_set_uint8(x_11, sizeof(void*)*3, x_216);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_11);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_12);
return x_221;
}
else
{
lean_object* x_222; uint8_t x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; uint8_t x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_222 = lean_ctor_get(x_11, 0);
x_223 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_224 = lean_ctor_get(x_11, 1);
x_225 = lean_ctor_get(x_11, 2);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_222);
lean_dec(x_11);
x_226 = 3;
x_227 = l_Lake_JobAction_merge(x_223, x_226);
x_228 = l_Lake_buildAction___redArg___closed__1;
x_229 = lean_array_get_size(x_222);
x_230 = lean_array_push(x_222, x_228);
x_231 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_224);
lean_ctor_set(x_231, 2, x_225);
lean_ctor_set_uint8(x_231, sizeof(void*)*3, x_227);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_229);
lean_ctor_set(x_232, 1, x_231);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_12);
return x_233;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_67; uint8_t x_72; 
x_72 = !lean_is_exclusive(x_9);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_73 = lean_ctor_get(x_9, 0);
x_74 = lean_ctor_get(x_9, 1);
x_75 = l_Lake_buildFileUnlessUpToDate_x27___closed__0;
lean_inc_ref(x_1);
x_76 = lean_string_append(x_1, x_75);
lean_inc_ref(x_76);
x_77 = l_Lake_readTraceFile(x_76, x_73, x_10);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec_ref(x_77);
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_82 = lean_ctor_get(x_74, 2);
lean_inc_ref(x_74);
lean_ctor_set(x_9, 0, x_81);
x_83 = l_Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0___redArg(x_1, x_74, x_80, x_82, x_8, x_9, x_79);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_84, 0);
x_86 = lean_unbox(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_83, 1);
lean_inc(x_87);
lean_dec_ref(x_83);
x_88 = lean_ctor_get(x_84, 1);
lean_inc(x_88);
lean_dec(x_84);
x_89 = 3;
lean_inc_ref(x_8);
lean_inc_ref(x_1);
x_90 = l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__3(x_2, x_1, x_4, x_74, x_76, x_89, x_5, x_6, x_7, x_8, x_88, x_87);
lean_dec_ref(x_76);
lean_dec_ref(x_74);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec_ref(x_90);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec_ref(x_91);
x_17 = x_93;
x_18 = x_92;
goto block_66;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_dec_ref(x_90);
x_95 = lean_ctor_get(x_91, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_91, 1);
lean_inc(x_96);
lean_dec_ref(x_91);
x_11 = x_95;
x_12 = x_96;
x_13 = x_94;
goto block_16;
}
}
else
{
lean_dec(x_84);
lean_dec_ref(x_76);
lean_dec_ref(x_74);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_67 = x_83;
goto block_71;
}
}
else
{
lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_97 = lean_ctor_get(x_9, 0);
x_98 = lean_ctor_get_uint8(x_9, sizeof(void*)*3);
x_99 = lean_ctor_get(x_9, 1);
x_100 = lean_ctor_get(x_9, 2);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_97);
lean_dec(x_9);
x_101 = l_Lake_buildFileUnlessUpToDate_x27___closed__0;
lean_inc_ref(x_1);
x_102 = lean_string_append(x_1, x_101);
lean_inc_ref(x_102);
x_103 = l_Lake_readTraceFile(x_102, x_97, x_10);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec_ref(x_103);
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
lean_dec(x_104);
x_108 = lean_ctor_get(x_99, 2);
lean_inc_ref(x_99);
x_109 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_99);
lean_ctor_set(x_109, 2, x_100);
lean_ctor_set_uint8(x_109, sizeof(void*)*3, x_98);
x_110 = l_Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0___redArg(x_1, x_99, x_106, x_108, x_8, x_109, x_105);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_111, 0);
x_113 = lean_unbox(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; 
x_114 = lean_ctor_get(x_110, 1);
lean_inc(x_114);
lean_dec_ref(x_110);
x_115 = lean_ctor_get(x_111, 1);
lean_inc(x_115);
lean_dec(x_111);
x_116 = 3;
lean_inc_ref(x_8);
lean_inc_ref(x_1);
x_117 = l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__3(x_2, x_1, x_4, x_99, x_102, x_116, x_5, x_6, x_7, x_8, x_115, x_114);
lean_dec_ref(x_102);
lean_dec_ref(x_99);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec_ref(x_117);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec_ref(x_118);
x_17 = x_120;
x_18 = x_119;
goto block_66;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_121 = lean_ctor_get(x_117, 1);
lean_inc(x_121);
lean_dec_ref(x_117);
x_122 = lean_ctor_get(x_118, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_118, 1);
lean_inc(x_123);
lean_dec_ref(x_118);
x_11 = x_122;
x_12 = x_123;
x_13 = x_121;
goto block_16;
}
}
else
{
lean_dec(x_111);
lean_dec_ref(x_102);
lean_dec_ref(x_99);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_67 = x_110;
goto block_71;
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
block_66:
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Lake_fetchFileTrace___redArg(x_1, x_3, x_8, x_17, x_18);
lean_dec_ref(x_8);
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
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get_uint8(x_21, sizeof(void*)*3);
x_32 = lean_ctor_get(x_21, 2);
lean_inc(x_32);
lean_inc(x_30);
lean_dec(x_21);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_25);
lean_ctor_set(x_34, 2, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*3, x_31);
lean_ctor_set(x_20, 1, x_34);
lean_ctor_set(x_20, 0, x_33);
return x_19;
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_20, 0);
lean_inc(x_35);
lean_dec(x_20);
x_36 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_36);
x_37 = lean_ctor_get_uint8(x_21, sizeof(void*)*3);
x_38 = lean_ctor_get(x_21, 2);
lean_inc(x_38);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 x_39 = x_21;
} else {
 lean_dec_ref(x_21);
 x_39 = lean_box(0);
}
x_40 = lean_box(0);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 3, 1);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_35);
lean_ctor_set(x_41, 2, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*3, x_37);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_19, 0, x_42);
return x_19;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_43 = lean_ctor_get(x_19, 1);
lean_inc(x_43);
lean_dec(x_19);
x_44 = lean_ctor_get(x_20, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_45 = x_20;
} else {
 lean_dec_ref(x_20);
 x_45 = lean_box(0);
}
x_46 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_46);
x_47 = lean_ctor_get_uint8(x_21, sizeof(void*)*3);
x_48 = lean_ctor_get(x_21, 2);
lean_inc(x_48);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 x_49 = x_21;
} else {
 lean_dec_ref(x_21);
 x_49 = lean_box(0);
}
x_50 = lean_box(0);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 3, 1);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_46);
lean_ctor_set(x_51, 1, x_44);
lean_ctor_set(x_51, 2, x_48);
lean_ctor_set_uint8(x_51, sizeof(void*)*3, x_47);
if (lean_is_scalar(x_45)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_45;
}
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_43);
return x_53;
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_19);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_19, 0);
lean_dec(x_55);
x_56 = !lean_is_exclusive(x_20);
if (x_56 == 0)
{
return x_19;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_20, 0);
x_58 = lean_ctor_get(x_20, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_20);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_19, 0, x_59);
return x_19;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_19, 1);
lean_inc(x_60);
lean_dec(x_19);
x_61 = lean_ctor_get(x_20, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_20, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_63 = x_20;
} else {
 lean_dec_ref(x_20);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_60);
return x_65;
}
}
}
block_71:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec_ref(x_67);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_17 = x_70;
x_18 = x_69;
goto block_66;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_MTime_checkUpToDate___at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__3___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__3___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
x_14 = l_Lake_buildAction___at___Lake_buildFileUnlessUpToDate_x27_spec__3(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
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
x_12 = l_Lake_buildFileUnlessUpToDate_x27(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
if (x_4 == 0)
{
lean_object* x_7; 
x_7 = l_IO_FS_readBinFile(x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint64_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_18; lean_object* x_32; 
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
x_11 = lean_byte_array_hash(x_8);
x_12 = l_Lake_Cache_artifactPath(x_1, x_11, x_3);
x_32 = l_Lake_createParentDirs(x_12, x_9);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = l_IO_FS_writeBinFile(x_12, x_8, x_33);
lean_dec(x_8);
if (lean_obj_tag(x_34) == 0)
{
if (x_5 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec_ref(x_34);
x_18 = x_35;
goto block_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec_ref(x_34);
x_37 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_37, 0, x_5);
lean_ctor_set_uint8(x_37, 1, x_5);
lean_ctor_set_uint8(x_37, 2, x_5);
lean_inc_ref_n(x_37, 2);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_37);
x_39 = l_IO_setAccessRights(x_12, x_38, x_36);
lean_dec_ref(x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec_ref(x_39);
x_18 = x_40;
goto block_31;
}
else
{
uint8_t x_41; 
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec_ref(x_2);
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_39, 0);
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_39);
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
uint8_t x_45; 
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec_ref(x_2);
x_45 = !lean_is_exclusive(x_34);
if (x_45 == 0)
{
return x_34;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_34, 0);
x_47 = lean_ctor_get(x_34, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_34);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_2);
x_49 = !lean_is_exclusive(x_32);
if (x_49 == 0)
{
return x_32;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_32, 0);
x_51 = lean_ctor_get(x_32, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_32);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 2, x_14);
lean_ctor_set_uint64(x_15, sizeof(void*)*3, x_11);
if (lean_is_scalar(x_10)) {
 x_16 = lean_alloc_ctor(0, 2, 0);
} else {
 x_16 = x_10;
}
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
block_31:
{
lean_object* x_19; 
lean_inc_ref(x_2);
x_19 = l_Lake_writeFileHash(x_2, x_11, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_io_metadata(x_12, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_24);
lean_dec(x_22);
x_13 = x_23;
x_14 = x_24;
goto block_17;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec_ref(x_21);
x_26 = l_Lake_platformTrace___closed__6;
x_13 = x_25;
x_14 = x_26;
goto block_17;
}
}
else
{
uint8_t x_27; 
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec_ref(x_2);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
else
{
uint8_t x_53; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_53 = !lean_is_exclusive(x_7);
if (x_53 == 0)
{
return x_7;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_7, 0);
x_55 = lean_ctor_get(x_7, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_7);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; 
x_57 = l_IO_FS_readFile(x_2, x_6);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_71; 
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
x_61 = l_String_crlfToLf(x_58);
lean_dec(x_58);
x_62 = l_Lake_platformTrace___closed__1;
x_63 = lean_string_hash(x_61);
x_64 = lean_uint64_mix_hash(x_62, x_63);
x_65 = l_Lake_Cache_artifactPath(x_1, x_64, x_3);
x_71 = l_Lake_createParentDirs(x_65, x_59);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec_ref(x_71);
x_73 = l_IO_FS_writeFile(x_65, x_61, x_72);
lean_dec_ref(x_61);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec_ref(x_73);
lean_inc_ref(x_2);
x_75 = l_Lake_writeFileHash(x_2, x_64, x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec_ref(x_75);
x_77 = lean_io_metadata(x_65, x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec_ref(x_77);
x_80 = lean_ctor_get(x_78, 1);
lean_inc_ref(x_80);
lean_dec(x_78);
x_66 = x_79;
x_67 = x_80;
goto block_70;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_77, 1);
lean_inc(x_81);
lean_dec_ref(x_77);
x_82 = l_Lake_platformTrace___closed__6;
x_66 = x_81;
x_67 = x_82;
goto block_70;
}
}
else
{
uint8_t x_83; 
lean_dec_ref(x_65);
lean_dec(x_60);
lean_dec_ref(x_2);
x_83 = !lean_is_exclusive(x_75);
if (x_83 == 0)
{
return x_75;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_75, 0);
x_85 = lean_ctor_get(x_75, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_75);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec_ref(x_65);
lean_dec(x_60);
lean_dec_ref(x_2);
x_87 = !lean_is_exclusive(x_73);
if (x_87 == 0)
{
return x_73;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_73, 0);
x_89 = lean_ctor_get(x_73, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_73);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec_ref(x_65);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_2);
x_91 = !lean_is_exclusive(x_71);
if (x_91 == 0)
{
return x_71;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_71, 0);
x_93 = lean_ctor_get(x_71, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_71);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
block_70:
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_2);
lean_ctor_set(x_68, 2, x_67);
lean_ctor_set_uint64(x_68, sizeof(void*)*3, x_64);
if (lean_is_scalar(x_60)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_60;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
return x_69;
}
}
else
{
uint8_t x_95; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_95 = !lean_is_exclusive(x_57);
if (x_95 == 0)
{
return x_57;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_57, 0);
x_97 = lean_ctor_get(x_57, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_57);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_saveArtifact___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_4);
x_8 = lean_unbox(x_5);
x_9 = l_Lake_Cache_saveArtifact(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_box(x_3);
x_8 = lean_box(x_4);
x_9 = lean_alloc_closure((void*)(l_Lake_Cache_saveArtifact___boxed), 6, 5);
lean_closure_set(x_9, 0, x_6);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_2);
lean_closure_set(x_9, 3, x_7);
lean_closure_set(x_9, 4, x_8);
x_10 = lean_apply_2(x_5, lean_box(0), x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec_ref(x_3);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_alloc_closure((void*)(l_Lake_cacheArtifact___redArg___lam__0___boxed), 1, 0);
x_13 = lean_box(x_6);
x_14 = lean_box(x_7);
x_15 = lean_alloc_closure((void*)(l_Lake_cacheArtifact___redArg___lam__1___boxed), 6, 5);
lean_closure_set(x_15, 0, x_4);
lean_closure_set(x_15, 1, x_5);
lean_closure_set(x_15, 2, x_13);
lean_closure_set(x_15, 3, x_14);
lean_closure_set(x_15, 4, x_2);
x_16 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_12, x_1);
x_17 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_16, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, uint8_t x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec_ref(x_4);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_alloc_closure((void*)(l_Lake_cacheArtifact___redArg___lam__0___boxed), 1, 0);
x_14 = lean_box(x_7);
x_15 = lean_box(x_8);
x_16 = lean_alloc_closure((void*)(l_Lake_cacheArtifact___redArg___lam__1___boxed), 6, 5);
lean_closure_set(x_16, 0, x_5);
lean_closure_set(x_16, 1, x_6);
lean_closure_set(x_16, 2, x_14);
lean_closure_set(x_16, 3, x_15);
lean_closure_set(x_16, 4, x_3);
x_17 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_13, x_2);
x_18 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_17, x_16);
return x_18;
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
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_3);
x_8 = lean_unbox(x_4);
x_9 = l_Lake_cacheArtifact___redArg___lam__1(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
x_10 = l_Lake_cacheArtifact___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheArtifact___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_7);
x_10 = lean_unbox(x_8);
x_11 = l_Lake_cacheArtifact(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArtifactTrace(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_11; 
x_11 = lean_io_metadata(x_2, x_4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_14);
lean_dec(x_12);
x_5 = x_13;
x_6 = x_14;
goto block_10;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec_ref(x_11);
x_16 = l_Lake_platformTrace___closed__6;
x_5 = x_15;
x_6 = x_16;
goto block_10;
}
block_10:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lake_platformTrace___closed__4;
x_8 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_6);
lean_ctor_set_uint64(x_8, sizeof(void*)*3, x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
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
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_ResolveArtifacts_ctorIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(0u);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_ResolveArtifacts_ctorIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_ResolveArtifacts_ctorIdx(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
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
LEAN_EXPORT lean_object* l_Lake_resolveArtifactsUsing_x3f___redArg(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_73 = lean_st_ref_take(x_6, x_13);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec_ref(x_73);
lean_inc(x_74);
x_76 = lean_st_ref_set(x_6, x_74, x_75);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec_ref(x_76);
x_78 = lean_ctor_get(x_12, 0);
x_79 = lean_ctor_get_uint8(x_12, sizeof(void*)*3);
x_80 = lean_ctor_get(x_12, 1);
x_81 = lean_ctor_get(x_12, 2);
x_82 = l_Lake_CacheMap_get_x3f(x_3, x_74);
lean_dec(x_74);
if (lean_obj_tag(x_82) == 0)
{
x_20 = x_7;
x_21 = x_8;
x_22 = x_9;
x_23 = x_10;
x_24 = x_11;
x_25 = x_12;
x_26 = x_77;
goto block_72;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
lean_inc_ref(x_1);
lean_inc(x_83);
x_84 = lean_apply_1(x_1, x_83);
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_85; 
lean_dec_ref(x_84);
lean_dec(x_83);
lean_inc(x_81);
lean_inc_ref(x_80);
lean_inc_ref(x_78);
x_85 = !lean_is_exclusive(x_12);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; 
x_86 = lean_ctor_get(x_12, 2);
lean_dec(x_86);
x_87 = lean_ctor_get(x_12, 1);
lean_dec(x_87);
x_88 = lean_ctor_get(x_12, 0);
lean_dec(x_88);
x_89 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__0;
x_90 = lean_uint64_to_nat(x_3);
x_91 = l_Nat_reprFast(x_90);
x_92 = lean_unsigned_to_nat(7u);
x_93 = lean_unsigned_to_nat(0u);
x_94 = lean_string_utf8_byte_size(x_91);
lean_inc_ref(x_91);
x_95 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_95, 0, x_91);
lean_ctor_set(x_95, 1, x_93);
lean_ctor_set(x_95, 2, x_94);
x_96 = l_Substring_nextn(x_95, x_92, x_93);
lean_dec_ref(x_95);
x_97 = lean_string_utf8_extract(x_91, x_93, x_96);
lean_dec(x_96);
lean_dec_ref(x_91);
x_98 = lean_string_append(x_89, x_97);
lean_dec_ref(x_97);
x_99 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__1;
x_100 = lean_string_append(x_98, x_99);
x_101 = 2;
x_102 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set_uint8(x_102, sizeof(void*)*1, x_101);
x_103 = lean_array_push(x_78, x_102);
lean_ctor_set(x_12, 0, x_103);
x_20 = x_7;
x_21 = x_8;
x_22 = x_9;
x_23 = x_10;
x_24 = x_11;
x_25 = x_12;
x_26 = x_77;
goto block_72;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_12);
x_104 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__0;
x_105 = lean_uint64_to_nat(x_3);
x_106 = l_Nat_reprFast(x_105);
x_107 = lean_unsigned_to_nat(7u);
x_108 = lean_unsigned_to_nat(0u);
x_109 = lean_string_utf8_byte_size(x_106);
lean_inc_ref(x_106);
x_110 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_110, 0, x_106);
lean_ctor_set(x_110, 1, x_108);
lean_ctor_set(x_110, 2, x_109);
x_111 = l_Substring_nextn(x_110, x_107, x_108);
lean_dec_ref(x_110);
x_112 = lean_string_utf8_extract(x_106, x_108, x_111);
lean_dec(x_111);
lean_dec_ref(x_106);
x_113 = lean_string_append(x_104, x_112);
lean_dec_ref(x_112);
x_114 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__1;
x_115 = lean_string_append(x_113, x_114);
x_116 = 2;
x_117 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set_uint8(x_117, sizeof(void*)*1, x_116);
x_118 = lean_array_push(x_78, x_117);
x_119 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_80);
lean_ctor_set(x_119, 2, x_81);
lean_ctor_set_uint8(x_119, sizeof(void*)*3, x_79);
x_20 = x_7;
x_21 = x_8;
x_22 = x_9;
x_23 = x_10;
x_24 = x_11;
x_25 = x_119;
x_26 = x_77;
goto block_72;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec_ref(x_1);
x_120 = lean_ctor_get(x_84, 0);
lean_inc(x_120);
lean_dec_ref(x_84);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_121 = lean_apply_8(x_2, x_120, x_7, x_8, x_9, x_10, x_11, x_12, x_77);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
if (lean_obj_tag(x_123) == 0)
{
uint8_t x_124; 
lean_dec(x_83);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
x_124 = !lean_is_exclusive(x_122);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_125 = lean_ctor_get(x_122, 1);
x_126 = lean_ctor_get(x_122, 0);
lean_dec(x_126);
x_127 = !lean_is_exclusive(x_121);
if (x_127 == 0)
{
lean_object* x_128; uint8_t x_129; 
x_128 = lean_ctor_get(x_121, 0);
lean_dec(x_128);
x_129 = !lean_is_exclusive(x_125);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; lean_object* x_145; 
x_130 = lean_ctor_get(x_125, 0);
x_131 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__0;
x_132 = lean_uint64_to_nat(x_3);
x_133 = l_Nat_reprFast(x_132);
x_134 = lean_unsigned_to_nat(7u);
x_135 = lean_unsigned_to_nat(0u);
x_136 = lean_string_utf8_byte_size(x_133);
lean_inc_ref(x_133);
x_137 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_137, 0, x_133);
lean_ctor_set(x_137, 1, x_135);
lean_ctor_set(x_137, 2, x_136);
x_138 = l_Substring_nextn(x_137, x_134, x_135);
lean_dec_ref(x_137);
x_139 = lean_string_utf8_extract(x_133, x_135, x_138);
lean_dec(x_138);
lean_dec_ref(x_133);
x_140 = lean_string_append(x_131, x_139);
lean_dec_ref(x_139);
x_141 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__2;
x_142 = lean_string_append(x_140, x_141);
x_143 = 2;
x_144 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set_uint8(x_144, sizeof(void*)*1, x_143);
x_145 = lean_array_push(x_130, x_144);
lean_ctor_set(x_125, 0, x_145);
return x_121;
}
else
{
lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_146 = lean_ctor_get(x_125, 0);
x_147 = lean_ctor_get_uint8(x_125, sizeof(void*)*3);
x_148 = lean_ctor_get(x_125, 1);
x_149 = lean_ctor_get(x_125, 2);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_146);
lean_dec(x_125);
x_150 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__0;
x_151 = lean_uint64_to_nat(x_3);
x_152 = l_Nat_reprFast(x_151);
x_153 = lean_unsigned_to_nat(7u);
x_154 = lean_unsigned_to_nat(0u);
x_155 = lean_string_utf8_byte_size(x_152);
lean_inc_ref(x_152);
x_156 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_156, 0, x_152);
lean_ctor_set(x_156, 1, x_154);
lean_ctor_set(x_156, 2, x_155);
x_157 = l_Substring_nextn(x_156, x_153, x_154);
lean_dec_ref(x_156);
x_158 = lean_string_utf8_extract(x_152, x_154, x_157);
lean_dec(x_157);
lean_dec_ref(x_152);
x_159 = lean_string_append(x_150, x_158);
lean_dec_ref(x_158);
x_160 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__2;
x_161 = lean_string_append(x_159, x_160);
x_162 = 2;
x_163 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set_uint8(x_163, sizeof(void*)*1, x_162);
x_164 = lean_array_push(x_146, x_163);
x_165 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_148);
lean_ctor_set(x_165, 2, x_149);
lean_ctor_set_uint8(x_165, sizeof(void*)*3, x_147);
lean_ctor_set(x_122, 1, x_165);
return x_121;
}
}
else
{
lean_object* x_166; lean_object* x_167; uint8_t x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_166 = lean_ctor_get(x_121, 1);
lean_inc(x_166);
lean_dec(x_121);
x_167 = lean_ctor_get(x_125, 0);
lean_inc_ref(x_167);
x_168 = lean_ctor_get_uint8(x_125, sizeof(void*)*3);
x_169 = lean_ctor_get(x_125, 1);
lean_inc_ref(x_169);
x_170 = lean_ctor_get(x_125, 2);
lean_inc(x_170);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 lean_ctor_release(x_125, 2);
 x_171 = x_125;
} else {
 lean_dec_ref(x_125);
 x_171 = lean_box(0);
}
x_172 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__0;
x_173 = lean_uint64_to_nat(x_3);
x_174 = l_Nat_reprFast(x_173);
x_175 = lean_unsigned_to_nat(7u);
x_176 = lean_unsigned_to_nat(0u);
x_177 = lean_string_utf8_byte_size(x_174);
lean_inc_ref(x_174);
x_178 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_178, 0, x_174);
lean_ctor_set(x_178, 1, x_176);
lean_ctor_set(x_178, 2, x_177);
x_179 = l_Substring_nextn(x_178, x_175, x_176);
lean_dec_ref(x_178);
x_180 = lean_string_utf8_extract(x_174, x_176, x_179);
lean_dec(x_179);
lean_dec_ref(x_174);
x_181 = lean_string_append(x_172, x_180);
lean_dec_ref(x_180);
x_182 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__2;
x_183 = lean_string_append(x_181, x_182);
x_184 = 2;
x_185 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set_uint8(x_185, sizeof(void*)*1, x_184);
x_186 = lean_array_push(x_167, x_185);
if (lean_is_scalar(x_171)) {
 x_187 = lean_alloc_ctor(0, 3, 1);
} else {
 x_187 = x_171;
}
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_169);
lean_ctor_set(x_187, 2, x_170);
lean_ctor_set_uint8(x_187, sizeof(void*)*3, x_168);
lean_ctor_set(x_122, 1, x_187);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_122);
lean_ctor_set(x_188, 1, x_166);
return x_188;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_189 = lean_ctor_get(x_122, 1);
lean_inc(x_189);
lean_dec(x_122);
x_190 = lean_ctor_get(x_121, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_191 = x_121;
} else {
 lean_dec_ref(x_121);
 x_191 = lean_box(0);
}
x_192 = lean_ctor_get(x_189, 0);
lean_inc_ref(x_192);
x_193 = lean_ctor_get_uint8(x_189, sizeof(void*)*3);
x_194 = lean_ctor_get(x_189, 1);
lean_inc_ref(x_194);
x_195 = lean_ctor_get(x_189, 2);
lean_inc(x_195);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 lean_ctor_release(x_189, 2);
 x_196 = x_189;
} else {
 lean_dec_ref(x_189);
 x_196 = lean_box(0);
}
x_197 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__0;
x_198 = lean_uint64_to_nat(x_3);
x_199 = l_Nat_reprFast(x_198);
x_200 = lean_unsigned_to_nat(7u);
x_201 = lean_unsigned_to_nat(0u);
x_202 = lean_string_utf8_byte_size(x_199);
lean_inc_ref(x_199);
x_203 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_203, 0, x_199);
lean_ctor_set(x_203, 1, x_201);
lean_ctor_set(x_203, 2, x_202);
x_204 = l_Substring_nextn(x_203, x_200, x_201);
lean_dec_ref(x_203);
x_205 = lean_string_utf8_extract(x_199, x_201, x_204);
lean_dec(x_204);
lean_dec_ref(x_199);
x_206 = lean_string_append(x_197, x_205);
lean_dec_ref(x_205);
x_207 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__2;
x_208 = lean_string_append(x_206, x_207);
x_209 = 2;
x_210 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set_uint8(x_210, sizeof(void*)*1, x_209);
x_211 = lean_array_push(x_192, x_210);
if (lean_is_scalar(x_196)) {
 x_212 = lean_alloc_ctor(0, 3, 1);
} else {
 x_212 = x_196;
}
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_194);
lean_ctor_set(x_212, 2, x_195);
lean_ctor_set_uint8(x_212, sizeof(void*)*3, x_193);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_123);
lean_ctor_set(x_213, 1, x_212);
if (lean_is_scalar(x_191)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_191;
}
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_190);
return x_214;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_215 = lean_ctor_get(x_121, 1);
lean_inc(x_215);
lean_dec_ref(x_121);
x_216 = lean_ctor_get(x_122, 1);
lean_inc(x_216);
lean_dec_ref(x_122);
x_217 = l_Lake_SavedTrace_replayOrFetch(x_4, x_3, x_83, x_5, x_7, x_8, x_9, x_10, x_11, x_216, x_215);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
if (lean_obj_tag(x_218) == 0)
{
uint8_t x_219; 
x_219 = !lean_is_exclusive(x_217);
if (x_219 == 0)
{
lean_object* x_220; uint8_t x_221; 
x_220 = lean_ctor_get(x_217, 0);
lean_dec(x_220);
x_221 = !lean_is_exclusive(x_218);
if (x_221 == 0)
{
lean_object* x_222; 
x_222 = lean_ctor_get(x_218, 0);
lean_dec(x_222);
lean_ctor_set(x_218, 0, x_123);
return x_217;
}
else
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_ctor_get(x_218, 1);
lean_inc(x_223);
lean_dec(x_218);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_123);
lean_ctor_set(x_224, 1, x_223);
lean_ctor_set(x_217, 0, x_224);
return x_217;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_225 = lean_ctor_get(x_217, 1);
lean_inc(x_225);
lean_dec(x_217);
x_226 = lean_ctor_get(x_218, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_227 = x_218;
} else {
 lean_dec_ref(x_218);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_123);
lean_ctor_set(x_228, 1, x_226);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_225);
return x_229;
}
}
else
{
uint8_t x_230; 
lean_dec_ref(x_123);
x_230 = !lean_is_exclusive(x_217);
if (x_230 == 0)
{
lean_object* x_231; uint8_t x_232; 
x_231 = lean_ctor_get(x_217, 0);
lean_dec(x_231);
x_232 = !lean_is_exclusive(x_218);
if (x_232 == 0)
{
return x_217;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_218, 0);
x_234 = lean_ctor_get(x_218, 1);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_218);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
lean_ctor_set(x_217, 0, x_235);
return x_217;
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_236 = lean_ctor_get(x_217, 1);
lean_inc(x_236);
lean_dec(x_217);
x_237 = lean_ctor_get(x_218, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_218, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_239 = x_218;
} else {
 lean_dec_ref(x_218);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_237);
lean_ctor_set(x_240, 1, x_238);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_236);
return x_241;
}
}
}
}
else
{
lean_dec_ref(x_122);
lean_dec(x_83);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
return x_121;
}
}
}
block_19:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
block_72:
{
if (lean_obj_tag(x_5) == 2)
{
lean_object* x_27; uint64_t x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_5, 0);
x_28 = lean_ctor_get_uint64(x_27, sizeof(void*)*3);
x_29 = lean_ctor_get(x_27, 1);
x_30 = lean_uint64_dec_eq(x_28, x_3);
if (x_30 == 0)
{
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_14 = x_25;
x_15 = x_26;
goto block_19;
}
else
{
if (lean_obj_tag(x_29) == 0)
{
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_14 = x_25;
x_15 = x_26;
goto block_19;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_inc(x_31);
x_32 = lean_apply_1(x_1, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_dec_ref(x_32);
lean_dec(x_31);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_14 = x_25;
x_15 = x_26;
goto block_19;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
lean_inc_ref(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc_ref(x_20);
x_34 = lean_apply_8(x_2, x_33, x_20, x_21, x_22, x_23, x_24, x_25, x_26);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_31);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_5);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec_ref(x_34);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec_ref(x_35);
x_14 = x_38;
x_15 = x_37;
goto block_19;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_inc_ref(x_36);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_dec_ref(x_34);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_dec_ref(x_35);
x_41 = lean_st_ref_take(x_6, x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec_ref(x_41);
lean_inc(x_31);
x_44 = l_Lake_CacheMap_insertCore(x_3, x_31, x_42);
x_45 = lean_st_ref_set(x_6, x_44, x_43);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = l_Lake_SavedTrace_replayOrFetch(x_4, x_3, x_31, x_5, x_20, x_21, x_22, x_23, x_24, x_40, x_46);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_5);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_47);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_47, 0);
lean_dec(x_50);
x_51 = !lean_is_exclusive(x_48);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_48, 0);
lean_dec(x_52);
lean_ctor_set(x_48, 0, x_36);
return x_47;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
lean_dec(x_48);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_36);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_47, 0, x_54);
return x_47;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_47, 1);
lean_inc(x_55);
lean_dec(x_47);
x_56 = lean_ctor_get(x_48, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_57 = x_48;
} else {
 lean_dec_ref(x_48);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_36);
lean_ctor_set(x_58, 1, x_56);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_55);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec_ref(x_36);
x_60 = !lean_is_exclusive(x_47);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_47, 0);
lean_dec(x_61);
x_62 = !lean_is_exclusive(x_48);
if (x_62 == 0)
{
return x_47;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_48, 0);
x_64 = lean_ctor_get(x_48, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_48);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_47, 0, x_65);
return x_47;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = lean_ctor_get(x_47, 1);
lean_inc(x_66);
lean_dec(x_47);
x_67 = lean_ctor_get(x_48, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_48, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_69 = x_48;
} else {
 lean_dec_ref(x_48);
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
return x_71;
}
}
}
}
else
{
lean_dec_ref(x_35);
lean_dec(x_31);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_5);
return x_34;
}
}
}
}
}
else
{
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_14 = x_25;
x_15 = x_26;
goto block_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifactsUsing_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint64_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lake_resolveArtifactsUsing_x3f___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifactsUsing_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint64_t x_14; lean_object* x_15; 
x_14 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_15 = l_Lake_resolveArtifactsUsing_x3f___redArg(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec_ref(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifactsUsing_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint64_t x_16; lean_object* x_17; 
x_16 = lean_unbox_uint64(x_5);
lean_dec(x_5);
x_17 = l_Lake_resolveArtifactsUsing_x3f(x_1, x_2, x_3, x_4, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_8);
lean_dec_ref(x_6);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_FileOutputHash_ctorIdx(lean_object* x_1, uint64_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_FileOutputHash_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_4 = l_Lake_FileOutputHash_ctorIdx(x_1, x_3);
lean_dec_ref(x_1);
return x_4;
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
lean_dec_ref(x_1);
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
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instResolveArtifactsFileOutputHashArtifactOfMonadLakeEnvOfMonadLiftTBaseIOOfMonad___redArg___lam__0(uint64_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 6);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
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
lean_dec_ref(x_4);
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
lean_inc_ref(x_1);
x_6 = l_Lake_fetchFileHash___redArg(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_21; 
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
x_21 = lean_io_metadata(x_1, x_8);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_24);
lean_dec(x_22);
x_13 = x_23;
x_14 = x_11;
x_15 = x_24;
goto block_20;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec_ref(x_21);
x_26 = l_Lake_platformTrace___closed__6;
x_13 = x_25;
x_14 = x_11;
x_15 = x_26;
goto block_20;
}
block_20:
{
lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; 
lean_inc_ref(x_1);
x_16 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_1);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_unbox_uint64(x_10);
lean_dec(x_10);
lean_ctor_set_uint64(x_16, sizeof(void*)*3, x_17);
if (lean_is_scalar(x_12)) {
 x_18 = lean_alloc_ctor(0, 2, 0);
} else {
 x_18 = x_12;
}
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_14);
if (lean_is_scalar(x_9)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_9;
}
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_13);
return x_19;
}
}
else
{
uint8_t x_27; 
lean_dec_ref(x_1);
x_27 = !lean_is_exclusive(x_6);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_6, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_7);
if (x_29 == 0)
{
return x_6;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_7, 0);
x_31 = lean_ctor_get(x_7, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_7);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_6, 0, x_32);
return x_6;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_6, 1);
lean_inc(x_33);
lean_dec(x_6);
x_34 = lean_ctor_get(x_7, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_7, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_36 = x_7;
} else {
 lean_dec_ref(x_7);
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
x_7 = l_Lake_fetchLocalArtifact___redArg(x_1, x_6, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchLocalArtifact___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_Lake_fetchLocalArtifact(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at_____private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lake_buildAction___at_____private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get_uint8(x_20, sizeof(void*)*1 + 2);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get_uint8(x_12, sizeof(void*)*3);
x_25 = lean_io_mono_ms_now(x_13);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = l_Lake_JobAction_merge(x_24, x_7);
lean_inc_ref(x_23);
lean_ctor_set_uint8(x_12, sizeof(void*)*3, x_28);
x_29 = lean_apply_7(x_1, x_4, x_8, x_9, x_10, x_11, x_12, x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec_ref(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_124; 
x_41 = lean_ctor_get(x_30, 1);
lean_inc(x_41);
lean_dec_ref(x_30);
x_42 = lean_ctor_get(x_41, 0);
x_43 = lean_ctor_get_uint8(x_41, sizeof(void*)*3);
x_44 = lean_ctor_get(x_41, 1);
x_45 = lean_ctor_get(x_41, 2);
lean_inc_ref(x_2);
x_124 = l_Lake_clearFileHash(x_2, x_31);
if (lean_obj_tag(x_124) == 0)
{
if (x_3 == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
lean_dec_ref(x_124);
x_126 = l_Lake_computeBinFileHash(x_2, x_125);
lean_dec_ref(x_2);
x_46 = x_126;
goto block_123;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_127);
lean_dec_ref(x_124);
x_128 = l_Lake_computeTextFileHash(x_2, x_127);
lean_dec_ref(x_2);
x_46 = x_128;
goto block_123;
}
}
else
{
uint8_t x_129; 
lean_inc(x_45);
lean_inc_ref(x_44);
lean_inc_ref(x_42);
lean_dec_ref(x_23);
lean_dec_ref(x_2);
x_129 = !lean_is_exclusive(x_41);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_130 = lean_ctor_get(x_41, 2);
lean_dec(x_130);
x_131 = lean_ctor_get(x_41, 1);
lean_dec(x_131);
x_132 = lean_ctor_get(x_41, 0);
lean_dec(x_132);
x_133 = lean_ctor_get(x_124, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_124, 1);
lean_inc(x_134);
lean_dec_ref(x_124);
x_135 = lean_io_error_to_string(x_133);
x_136 = 3;
x_137 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set_uint8(x_137, sizeof(void*)*1, x_136);
x_138 = lean_array_get_size(x_42);
x_139 = lean_array_push(x_42, x_137);
lean_ctor_set(x_41, 0, x_139);
x_32 = x_138;
x_33 = x_41;
x_34 = x_134;
goto block_40;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_41);
x_140 = lean_ctor_get(x_124, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_124, 1);
lean_inc(x_141);
lean_dec_ref(x_124);
x_142 = lean_io_error_to_string(x_140);
x_143 = 3;
x_144 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set_uint8(x_144, sizeof(void*)*1, x_143);
x_145 = lean_array_get_size(x_42);
x_146 = lean_array_push(x_42, x_144);
x_147 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_44);
lean_ctor_set(x_147, 2, x_45);
lean_ctor_set_uint8(x_147, sizeof(void*)*3, x_43);
x_32 = x_145;
x_33 = x_147;
x_34 = x_141;
goto block_40;
}
}
block_123:
{
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint64_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
x_49 = lean_array_get_size(x_23);
lean_dec_ref(x_23);
x_50 = lean_array_get_size(x_42);
lean_inc(x_50);
x_51 = l_Array_extract___redArg(x_42, x_49, x_50);
x_52 = lean_unbox_uint64(x_47);
x_53 = lean_uint64_to_nat(x_52);
x_54 = l_Lean_bignumToJson(x_53);
x_55 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_5, x_54, x_51);
x_56 = l_Lake_BuildMetadata_writeFile(x_6, x_55, x_48);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
lean_dec(x_50);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_58 = lean_ctor_get(x_56, 1);
x_59 = lean_ctor_get(x_56, 0);
lean_dec(x_59);
x_60 = lean_box(0);
lean_inc(x_47);
lean_ctor_set_tag(x_56, 1);
lean_ctor_set(x_56, 1, x_60);
lean_ctor_set(x_56, 0, x_47);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_56);
x_62 = l_Lake_buildAction___at_____private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(x_26, x_61, x_41, x_58);
lean_dec_ref(x_61);
lean_dec(x_26);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_62, 0);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_64, 0);
lean_dec(x_66);
lean_ctor_set(x_64, 0, x_47);
return x_62;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_47);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_62, 0, x_68);
return x_62;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_62, 0);
x_70 = lean_ctor_get(x_62, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_62);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_72 = x_69;
} else {
 lean_dec_ref(x_69);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_47);
lean_ctor_set(x_73, 1, x_71);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_70);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_75 = lean_ctor_get(x_56, 1);
lean_inc(x_75);
lean_dec(x_56);
x_76 = lean_box(0);
lean_inc(x_47);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_47);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = l_Lake_buildAction___at_____private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(x_26, x_78, x_41, x_75);
lean_dec_ref(x_78);
lean_dec(x_26);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_82 = x_79;
} else {
 lean_dec_ref(x_79);
 x_82 = lean_box(0);
}
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_84 = x_80;
} else {
 lean_dec_ref(x_80);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_47);
lean_ctor_set(x_85, 1, x_83);
if (lean_is_scalar(x_82)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_82;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_81);
return x_86;
}
}
else
{
uint8_t x_87; 
lean_dec(x_47);
lean_inc(x_45);
lean_inc_ref(x_44);
lean_inc_ref(x_42);
x_87 = !lean_is_exclusive(x_41);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; 
x_88 = lean_ctor_get(x_41, 2);
lean_dec(x_88);
x_89 = lean_ctor_get(x_41, 1);
lean_dec(x_89);
x_90 = lean_ctor_get(x_41, 0);
lean_dec(x_90);
x_91 = lean_ctor_get(x_56, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_56, 1);
lean_inc(x_92);
lean_dec_ref(x_56);
x_93 = lean_io_error_to_string(x_91);
x_94 = 3;
x_95 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set_uint8(x_95, sizeof(void*)*1, x_94);
x_96 = lean_array_push(x_42, x_95);
lean_ctor_set(x_41, 0, x_96);
x_32 = x_50;
x_33 = x_41;
x_34 = x_92;
goto block_40;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_41);
x_97 = lean_ctor_get(x_56, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_56, 1);
lean_inc(x_98);
lean_dec_ref(x_56);
x_99 = lean_io_error_to_string(x_97);
x_100 = 3;
x_101 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set_uint8(x_101, sizeof(void*)*1, x_100);
x_102 = lean_array_push(x_42, x_101);
x_103 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_44);
lean_ctor_set(x_103, 2, x_45);
lean_ctor_set_uint8(x_103, sizeof(void*)*3, x_43);
x_32 = x_50;
x_33 = x_103;
x_34 = x_98;
goto block_40;
}
}
}
else
{
uint8_t x_104; 
lean_inc(x_45);
lean_inc_ref(x_44);
lean_inc_ref(x_42);
lean_dec_ref(x_23);
x_104 = !lean_is_exclusive(x_41);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_105 = lean_ctor_get(x_41, 2);
lean_dec(x_105);
x_106 = lean_ctor_get(x_41, 1);
lean_dec(x_106);
x_107 = lean_ctor_get(x_41, 0);
lean_dec(x_107);
x_108 = lean_ctor_get(x_46, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_46, 1);
lean_inc(x_109);
lean_dec_ref(x_46);
x_110 = lean_io_error_to_string(x_108);
x_111 = 3;
x_112 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set_uint8(x_112, sizeof(void*)*1, x_111);
x_113 = lean_array_get_size(x_42);
x_114 = lean_array_push(x_42, x_112);
lean_ctor_set(x_41, 0, x_114);
x_32 = x_113;
x_33 = x_41;
x_34 = x_109;
goto block_40;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_41);
x_115 = lean_ctor_get(x_46, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_46, 1);
lean_inc(x_116);
lean_dec_ref(x_46);
x_117 = lean_io_error_to_string(x_115);
x_118 = 3;
x_119 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set_uint8(x_119, sizeof(void*)*1, x_118);
x_120 = lean_array_get_size(x_42);
x_121 = lean_array_push(x_42, x_119);
x_122 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_44);
lean_ctor_set(x_122, 2, x_45);
lean_ctor_set_uint8(x_122, sizeof(void*)*3, x_43);
x_32 = x_120;
x_33 = x_122;
x_34 = x_116;
goto block_40;
}
}
}
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_dec_ref(x_23);
lean_dec_ref(x_2);
x_148 = lean_ctor_get(x_30, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_30, 1);
lean_inc(x_149);
lean_dec_ref(x_30);
x_32 = x_148;
x_33 = x_149;
x_34 = x_31;
goto block_40;
}
block_40:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_box(0);
x_36 = l_Lake_buildAction___at_____private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(x_26, x_35, x_33, x_34);
lean_dec(x_26);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec_ref(x_36);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_14 = x_32;
x_15 = x_39;
x_16 = x_38;
goto block_19;
}
}
else
{
lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_150 = lean_ctor_get(x_12, 0);
x_151 = lean_ctor_get_uint8(x_12, sizeof(void*)*3);
x_152 = lean_ctor_get(x_12, 1);
x_153 = lean_ctor_get(x_12, 2);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_150);
lean_dec(x_12);
x_154 = lean_io_mono_ms_now(x_13);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec_ref(x_154);
x_157 = l_Lake_JobAction_merge(x_151, x_7);
lean_inc_ref(x_150);
x_158 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_158, 0, x_150);
lean_ctor_set(x_158, 1, x_152);
lean_ctor_set(x_158, 2, x_153);
lean_ctor_set_uint8(x_158, sizeof(void*)*3, x_157);
x_159 = lean_apply_7(x_1, x_4, x_8, x_9, x_10, x_11, x_158, x_156);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec_ref(x_159);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_218; 
x_171 = lean_ctor_get(x_160, 1);
lean_inc(x_171);
lean_dec_ref(x_160);
x_172 = lean_ctor_get(x_171, 0);
x_173 = lean_ctor_get_uint8(x_171, sizeof(void*)*3);
x_174 = lean_ctor_get(x_171, 1);
x_175 = lean_ctor_get(x_171, 2);
lean_inc_ref(x_2);
x_218 = l_Lake_clearFileHash(x_2, x_161);
if (lean_obj_tag(x_218) == 0)
{
if (x_3 == 0)
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_218, 1);
lean_inc(x_219);
lean_dec_ref(x_218);
x_220 = l_Lake_computeBinFileHash(x_2, x_219);
lean_dec_ref(x_2);
x_176 = x_220;
goto block_217;
}
else
{
lean_object* x_221; lean_object* x_222; 
x_221 = lean_ctor_get(x_218, 1);
lean_inc(x_221);
lean_dec_ref(x_218);
x_222 = l_Lake_computeTextFileHash(x_2, x_221);
lean_dec_ref(x_2);
x_176 = x_222;
goto block_217;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_inc(x_175);
lean_inc_ref(x_174);
lean_inc_ref(x_172);
lean_dec_ref(x_150);
lean_dec_ref(x_2);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 lean_ctor_release(x_171, 2);
 x_223 = x_171;
} else {
 lean_dec_ref(x_171);
 x_223 = lean_box(0);
}
x_224 = lean_ctor_get(x_218, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_218, 1);
lean_inc(x_225);
lean_dec_ref(x_218);
x_226 = lean_io_error_to_string(x_224);
x_227 = 3;
x_228 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set_uint8(x_228, sizeof(void*)*1, x_227);
x_229 = lean_array_get_size(x_172);
x_230 = lean_array_push(x_172, x_228);
if (lean_is_scalar(x_223)) {
 x_231 = lean_alloc_ctor(0, 3, 1);
} else {
 x_231 = x_223;
}
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_174);
lean_ctor_set(x_231, 2, x_175);
lean_ctor_set_uint8(x_231, sizeof(void*)*3, x_173);
x_162 = x_229;
x_163 = x_231;
x_164 = x_225;
goto block_170;
}
block_217:
{
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint64_t x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec_ref(x_176);
x_179 = lean_array_get_size(x_150);
lean_dec_ref(x_150);
x_180 = lean_array_get_size(x_172);
lean_inc(x_180);
x_181 = l_Array_extract___redArg(x_172, x_179, x_180);
x_182 = lean_unbox_uint64(x_177);
x_183 = lean_uint64_to_nat(x_182);
x_184 = l_Lean_bignumToJson(x_183);
x_185 = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(x_5, x_184, x_181);
x_186 = l_Lake_BuildMetadata_writeFile(x_6, x_185, x_178);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_180);
x_187 = lean_ctor_get(x_186, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_188 = x_186;
} else {
 lean_dec_ref(x_186);
 x_188 = lean_box(0);
}
x_189 = lean_box(0);
lean_inc(x_177);
if (lean_is_scalar(x_188)) {
 x_190 = lean_alloc_ctor(1, 2, 0);
} else {
 x_190 = x_188;
 lean_ctor_set_tag(x_190, 1);
}
lean_ctor_set(x_190, 0, x_177);
lean_ctor_set(x_190, 1, x_189);
x_191 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_191, 0, x_190);
x_192 = l_Lake_buildAction___at_____private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(x_155, x_191, x_171, x_187);
lean_dec_ref(x_191);
lean_dec(x_155);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_195 = x_192;
} else {
 lean_dec_ref(x_192);
 x_195 = lean_box(0);
}
x_196 = lean_ctor_get(x_193, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_197 = x_193;
} else {
 lean_dec_ref(x_193);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_177);
lean_ctor_set(x_198, 1, x_196);
if (lean_is_scalar(x_195)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_195;
}
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_194);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_177);
lean_inc(x_175);
lean_inc_ref(x_174);
lean_inc_ref(x_172);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 lean_ctor_release(x_171, 2);
 x_200 = x_171;
} else {
 lean_dec_ref(x_171);
 x_200 = lean_box(0);
}
x_201 = lean_ctor_get(x_186, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_186, 1);
lean_inc(x_202);
lean_dec_ref(x_186);
x_203 = lean_io_error_to_string(x_201);
x_204 = 3;
x_205 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set_uint8(x_205, sizeof(void*)*1, x_204);
x_206 = lean_array_push(x_172, x_205);
if (lean_is_scalar(x_200)) {
 x_207 = lean_alloc_ctor(0, 3, 1);
} else {
 x_207 = x_200;
}
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_174);
lean_ctor_set(x_207, 2, x_175);
lean_ctor_set_uint8(x_207, sizeof(void*)*3, x_173);
x_162 = x_180;
x_163 = x_207;
x_164 = x_202;
goto block_170;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_inc(x_175);
lean_inc_ref(x_174);
lean_inc_ref(x_172);
lean_dec_ref(x_150);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 lean_ctor_release(x_171, 2);
 x_208 = x_171;
} else {
 lean_dec_ref(x_171);
 x_208 = lean_box(0);
}
x_209 = lean_ctor_get(x_176, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_176, 1);
lean_inc(x_210);
lean_dec_ref(x_176);
x_211 = lean_io_error_to_string(x_209);
x_212 = 3;
x_213 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set_uint8(x_213, sizeof(void*)*1, x_212);
x_214 = lean_array_get_size(x_172);
x_215 = lean_array_push(x_172, x_213);
if (lean_is_scalar(x_208)) {
 x_216 = lean_alloc_ctor(0, 3, 1);
} else {
 x_216 = x_208;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_174);
lean_ctor_set(x_216, 2, x_175);
lean_ctor_set_uint8(x_216, sizeof(void*)*3, x_173);
x_162 = x_214;
x_163 = x_216;
x_164 = x_210;
goto block_170;
}
}
}
else
{
lean_object* x_232; lean_object* x_233; 
lean_dec_ref(x_150);
lean_dec_ref(x_2);
x_232 = lean_ctor_get(x_160, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_160, 1);
lean_inc(x_233);
lean_dec_ref(x_160);
x_162 = x_232;
x_163 = x_233;
x_164 = x_161;
goto block_170;
}
block_170:
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_165 = lean_box(0);
x_166 = l_Lake_buildAction___at_____private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(x_155, x_165, x_163, x_164);
lean_dec(x_155);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec_ref(x_166);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_14 = x_162;
x_15 = x_169;
x_16 = x_168;
goto block_19;
}
}
}
else
{
uint8_t x_234; 
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_234 = !lean_is_exclusive(x_12);
if (x_234 == 0)
{
lean_object* x_235; uint8_t x_236; uint8_t x_237; uint8_t x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_235 = lean_ctor_get(x_12, 0);
x_236 = lean_ctor_get_uint8(x_12, sizeof(void*)*3);
x_237 = 3;
x_238 = l_Lake_JobAction_merge(x_236, x_237);
x_239 = l_Lake_buildAction___redArg___closed__1;
x_240 = lean_array_get_size(x_235);
x_241 = lean_array_push(x_235, x_239);
lean_ctor_set(x_12, 0, x_241);
lean_ctor_set_uint8(x_12, sizeof(void*)*3, x_238);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_12);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_13);
return x_243;
}
else
{
lean_object* x_244; uint8_t x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; uint8_t x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_244 = lean_ctor_get(x_12, 0);
x_245 = lean_ctor_get_uint8(x_12, sizeof(void*)*3);
x_246 = lean_ctor_get(x_12, 1);
x_247 = lean_ctor_get(x_12, 2);
lean_inc(x_247);
lean_inc(x_246);
lean_inc(x_244);
lean_dec(x_12);
x_248 = 3;
x_249 = l_Lake_JobAction_merge(x_245, x_248);
x_250 = l_Lake_buildAction___redArg___closed__1;
x_251 = lean_array_get_size(x_244);
x_252 = lean_array_push(x_244, x_250);
x_253 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_246);
lean_ctor_set(x_253, 2, x_247);
lean_ctor_set_uint8(x_253, sizeof(void*)*3, x_249);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_251);
lean_ctor_set(x_254, 1, x_253);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_13);
return x_255;
}
}
block_19:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = 3;
x_14 = l_Lake_buildAction___at_____private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(x_2, x_1, x_3, x_6, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at_____private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_buildAction___at_____private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at_____private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_3);
x_15 = lean_unbox(x_7);
x_16 = l_Lake_buildAction___at_____private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild_spec__0(x_1, x_2, x_14, x_4, x_5, x_6, x_15, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
x_14 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifactsUsing_x3f___at___Lake_buildArtifactUnlessUpToDate_spec__0(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_73 = lean_st_ref_take(x_6, x_12);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec_ref(x_73);
lean_inc(x_74);
x_76 = lean_st_ref_set(x_6, x_74, x_75);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_78 = lean_ctor_get(x_76, 1);
x_79 = lean_ctor_get(x_76, 0);
lean_dec(x_79);
x_80 = lean_ctor_get(x_11, 0);
x_81 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_82 = lean_ctor_get(x_11, 1);
x_83 = lean_ctor_get(x_11, 2);
x_84 = l_Lake_CacheMap_get_x3f(x_3, x_74);
lean_dec(x_74);
if (lean_obj_tag(x_84) == 0)
{
lean_free_object(x_76);
x_19 = x_2;
x_20 = x_7;
x_21 = x_8;
x_22 = x_9;
x_23 = x_10;
x_24 = x_11;
x_25 = x_78;
goto block_72;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec_ref(x_84);
lean_inc(x_85);
x_86 = l_UInt64_fromJson_x3f(x_85);
if (lean_obj_tag(x_86) == 0)
{
uint8_t x_87; 
lean_dec_ref(x_86);
lean_dec(x_85);
lean_inc(x_83);
lean_inc_ref(x_82);
lean_inc_ref(x_80);
lean_free_object(x_76);
x_87 = !lean_is_exclusive(x_11);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; 
x_88 = lean_ctor_get(x_11, 2);
lean_dec(x_88);
x_89 = lean_ctor_get(x_11, 1);
lean_dec(x_89);
x_90 = lean_ctor_get(x_11, 0);
lean_dec(x_90);
x_91 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__0;
x_92 = lean_uint64_to_nat(x_3);
x_93 = l_Nat_reprFast(x_92);
x_94 = lean_unsigned_to_nat(7u);
x_95 = lean_unsigned_to_nat(0u);
x_96 = lean_string_utf8_byte_size(x_93);
lean_inc_ref(x_93);
x_97 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_97, 0, x_93);
lean_ctor_set(x_97, 1, x_95);
lean_ctor_set(x_97, 2, x_96);
x_98 = l_Substring_nextn(x_97, x_94, x_95);
lean_dec_ref(x_97);
x_99 = lean_string_utf8_extract(x_93, x_95, x_98);
lean_dec(x_98);
lean_dec_ref(x_93);
x_100 = lean_string_append(x_91, x_99);
lean_dec_ref(x_99);
x_101 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__1;
x_102 = lean_string_append(x_100, x_101);
x_103 = 2;
x_104 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set_uint8(x_104, sizeof(void*)*1, x_103);
x_105 = lean_array_push(x_80, x_104);
lean_ctor_set(x_11, 0, x_105);
x_19 = x_2;
x_20 = x_7;
x_21 = x_8;
x_22 = x_9;
x_23 = x_10;
x_24 = x_11;
x_25 = x_78;
goto block_72;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_11);
x_106 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__0;
x_107 = lean_uint64_to_nat(x_3);
x_108 = l_Nat_reprFast(x_107);
x_109 = lean_unsigned_to_nat(7u);
x_110 = lean_unsigned_to_nat(0u);
x_111 = lean_string_utf8_byte_size(x_108);
lean_inc_ref(x_108);
x_112 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_112, 0, x_108);
lean_ctor_set(x_112, 1, x_110);
lean_ctor_set(x_112, 2, x_111);
x_113 = l_Substring_nextn(x_112, x_109, x_110);
lean_dec_ref(x_112);
x_114 = lean_string_utf8_extract(x_108, x_110, x_113);
lean_dec(x_113);
lean_dec_ref(x_108);
x_115 = lean_string_append(x_106, x_114);
lean_dec_ref(x_114);
x_116 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__1;
x_117 = lean_string_append(x_115, x_116);
x_118 = 2;
x_119 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set_uint8(x_119, sizeof(void*)*1, x_118);
x_120 = lean_array_push(x_80, x_119);
x_121 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_82);
lean_ctor_set(x_121, 2, x_83);
lean_ctor_set_uint8(x_121, sizeof(void*)*3, x_81);
x_19 = x_2;
x_20 = x_7;
x_21 = x_8;
x_22 = x_9;
x_23 = x_10;
x_24 = x_121;
x_25 = x_78;
goto block_72;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint64_t x_126; lean_object* x_127; lean_object* x_128; 
x_122 = lean_ctor_get(x_10, 1);
x_123 = lean_ctor_get(x_122, 1);
x_124 = lean_ctor_get(x_86, 0);
lean_inc(x_124);
lean_dec_ref(x_86);
x_125 = lean_ctor_get(x_123, 6);
x_126 = lean_unbox_uint64(x_124);
lean_dec(x_124);
lean_inc_ref(x_125);
x_127 = l_Lake_Cache_getArtifact_x3f(x_125, x_126, x_1, x_78);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
uint8_t x_129; 
lean_dec(x_85);
lean_inc(x_83);
lean_inc_ref(x_82);
lean_inc_ref(x_80);
lean_dec_ref(x_10);
lean_dec(x_5);
x_129 = !lean_is_exclusive(x_11);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_130 = lean_ctor_get(x_11, 2);
lean_dec(x_130);
x_131 = lean_ctor_get(x_11, 1);
lean_dec(x_131);
x_132 = lean_ctor_get(x_11, 0);
lean_dec(x_132);
x_133 = !lean_is_exclusive(x_127);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; 
x_134 = lean_ctor_get(x_127, 0);
lean_dec(x_134);
x_135 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__0;
x_136 = lean_uint64_to_nat(x_3);
x_137 = l_Nat_reprFast(x_136);
x_138 = lean_unsigned_to_nat(7u);
x_139 = lean_unsigned_to_nat(0u);
x_140 = lean_string_utf8_byte_size(x_137);
lean_inc_ref(x_137);
x_141 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_141, 0, x_137);
lean_ctor_set(x_141, 1, x_139);
lean_ctor_set(x_141, 2, x_140);
x_142 = l_Substring_nextn(x_141, x_138, x_139);
lean_dec_ref(x_141);
x_143 = lean_string_utf8_extract(x_137, x_139, x_142);
lean_dec(x_142);
lean_dec_ref(x_137);
x_144 = lean_string_append(x_135, x_143);
lean_dec_ref(x_143);
x_145 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__2;
x_146 = lean_string_append(x_144, x_145);
x_147 = 2;
x_148 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set_uint8(x_148, sizeof(void*)*1, x_147);
x_149 = lean_array_push(x_80, x_148);
lean_ctor_set(x_11, 0, x_149);
lean_ctor_set(x_76, 1, x_11);
lean_ctor_set(x_76, 0, x_128);
lean_ctor_set(x_127, 0, x_76);
return x_127;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_150 = lean_ctor_get(x_127, 1);
lean_inc(x_150);
lean_dec(x_127);
x_151 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__0;
x_152 = lean_uint64_to_nat(x_3);
x_153 = l_Nat_reprFast(x_152);
x_154 = lean_unsigned_to_nat(7u);
x_155 = lean_unsigned_to_nat(0u);
x_156 = lean_string_utf8_byte_size(x_153);
lean_inc_ref(x_153);
x_157 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_157, 0, x_153);
lean_ctor_set(x_157, 1, x_155);
lean_ctor_set(x_157, 2, x_156);
x_158 = l_Substring_nextn(x_157, x_154, x_155);
lean_dec_ref(x_157);
x_159 = lean_string_utf8_extract(x_153, x_155, x_158);
lean_dec(x_158);
lean_dec_ref(x_153);
x_160 = lean_string_append(x_151, x_159);
lean_dec_ref(x_159);
x_161 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__2;
x_162 = lean_string_append(x_160, x_161);
x_163 = 2;
x_164 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set_uint8(x_164, sizeof(void*)*1, x_163);
x_165 = lean_array_push(x_80, x_164);
lean_ctor_set(x_11, 0, x_165);
lean_ctor_set(x_76, 1, x_11);
lean_ctor_set(x_76, 0, x_128);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_76);
lean_ctor_set(x_166, 1, x_150);
return x_166;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_11);
x_167 = lean_ctor_get(x_127, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_168 = x_127;
} else {
 lean_dec_ref(x_127);
 x_168 = lean_box(0);
}
x_169 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__0;
x_170 = lean_uint64_to_nat(x_3);
x_171 = l_Nat_reprFast(x_170);
x_172 = lean_unsigned_to_nat(7u);
x_173 = lean_unsigned_to_nat(0u);
x_174 = lean_string_utf8_byte_size(x_171);
lean_inc_ref(x_171);
x_175 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_175, 0, x_171);
lean_ctor_set(x_175, 1, x_173);
lean_ctor_set(x_175, 2, x_174);
x_176 = l_Substring_nextn(x_175, x_172, x_173);
lean_dec_ref(x_175);
x_177 = lean_string_utf8_extract(x_171, x_173, x_176);
lean_dec(x_176);
lean_dec_ref(x_171);
x_178 = lean_string_append(x_169, x_177);
lean_dec_ref(x_177);
x_179 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__2;
x_180 = lean_string_append(x_178, x_179);
x_181 = 2;
x_182 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set_uint8(x_182, sizeof(void*)*1, x_181);
x_183 = lean_array_push(x_80, x_182);
x_184 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_82);
lean_ctor_set(x_184, 2, x_83);
lean_ctor_set_uint8(x_184, sizeof(void*)*3, x_81);
lean_ctor_set(x_76, 1, x_184);
lean_ctor_set(x_76, 0, x_128);
if (lean_is_scalar(x_168)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_168;
}
lean_ctor_set(x_185, 0, x_76);
lean_ctor_set(x_185, 1, x_167);
return x_185;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_free_object(x_76);
x_186 = lean_ctor_get(x_127, 1);
lean_inc(x_186);
lean_dec_ref(x_127);
x_187 = l_Lake_SavedTrace_replayOrFetch(x_4, x_3, x_85, x_5, x_2, x_7, x_8, x_9, x_10, x_11, x_186);
lean_dec_ref(x_10);
lean_dec(x_5);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
if (lean_obj_tag(x_188) == 0)
{
uint8_t x_189; 
x_189 = !lean_is_exclusive(x_187);
if (x_189 == 0)
{
lean_object* x_190; uint8_t x_191; 
x_190 = lean_ctor_get(x_187, 0);
lean_dec(x_190);
x_191 = !lean_is_exclusive(x_188);
if (x_191 == 0)
{
lean_object* x_192; 
x_192 = lean_ctor_get(x_188, 0);
lean_dec(x_192);
lean_ctor_set(x_188, 0, x_128);
return x_187;
}
else
{
lean_object* x_193; lean_object* x_194; 
x_193 = lean_ctor_get(x_188, 1);
lean_inc(x_193);
lean_dec(x_188);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_128);
lean_ctor_set(x_194, 1, x_193);
lean_ctor_set(x_187, 0, x_194);
return x_187;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_195 = lean_ctor_get(x_187, 1);
lean_inc(x_195);
lean_dec(x_187);
x_196 = lean_ctor_get(x_188, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_197 = x_188;
} else {
 lean_dec_ref(x_188);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_128);
lean_ctor_set(x_198, 1, x_196);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_195);
return x_199;
}
}
else
{
uint8_t x_200; 
lean_dec_ref(x_128);
x_200 = !lean_is_exclusive(x_187);
if (x_200 == 0)
{
lean_object* x_201; uint8_t x_202; 
x_201 = lean_ctor_get(x_187, 0);
lean_dec(x_201);
x_202 = !lean_is_exclusive(x_188);
if (x_202 == 0)
{
return x_187;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_188, 0);
x_204 = lean_ctor_get(x_188, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_188);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
lean_ctor_set(x_187, 0, x_205);
return x_187;
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_206 = lean_ctor_get(x_187, 1);
lean_inc(x_206);
lean_dec(x_187);
x_207 = lean_ctor_get(x_188, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_188, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_209 = x_188;
} else {
 lean_dec_ref(x_188);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_208);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_206);
return x_211;
}
}
}
}
}
}
else
{
lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_212 = lean_ctor_get(x_76, 1);
lean_inc(x_212);
lean_dec(x_76);
x_213 = lean_ctor_get(x_11, 0);
x_214 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_215 = lean_ctor_get(x_11, 1);
x_216 = lean_ctor_get(x_11, 2);
x_217 = l_Lake_CacheMap_get_x3f(x_3, x_74);
lean_dec(x_74);
if (lean_obj_tag(x_217) == 0)
{
x_19 = x_2;
x_20 = x_7;
x_21 = x_8;
x_22 = x_9;
x_23 = x_10;
x_24 = x_11;
x_25 = x_212;
goto block_72;
}
else
{
lean_object* x_218; lean_object* x_219; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
lean_dec_ref(x_217);
lean_inc(x_218);
x_219 = l_UInt64_fromJson_x3f(x_218);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec_ref(x_219);
lean_dec(x_218);
lean_inc(x_216);
lean_inc_ref(x_215);
lean_inc_ref(x_213);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 x_220 = x_11;
} else {
 lean_dec_ref(x_11);
 x_220 = lean_box(0);
}
x_221 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__0;
x_222 = lean_uint64_to_nat(x_3);
x_223 = l_Nat_reprFast(x_222);
x_224 = lean_unsigned_to_nat(7u);
x_225 = lean_unsigned_to_nat(0u);
x_226 = lean_string_utf8_byte_size(x_223);
lean_inc_ref(x_223);
x_227 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_227, 0, x_223);
lean_ctor_set(x_227, 1, x_225);
lean_ctor_set(x_227, 2, x_226);
x_228 = l_Substring_nextn(x_227, x_224, x_225);
lean_dec_ref(x_227);
x_229 = lean_string_utf8_extract(x_223, x_225, x_228);
lean_dec(x_228);
lean_dec_ref(x_223);
x_230 = lean_string_append(x_221, x_229);
lean_dec_ref(x_229);
x_231 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__1;
x_232 = lean_string_append(x_230, x_231);
x_233 = 2;
x_234 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set_uint8(x_234, sizeof(void*)*1, x_233);
x_235 = lean_array_push(x_213, x_234);
if (lean_is_scalar(x_220)) {
 x_236 = lean_alloc_ctor(0, 3, 1);
} else {
 x_236 = x_220;
}
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_215);
lean_ctor_set(x_236, 2, x_216);
lean_ctor_set_uint8(x_236, sizeof(void*)*3, x_214);
x_19 = x_2;
x_20 = x_7;
x_21 = x_8;
x_22 = x_9;
x_23 = x_10;
x_24 = x_236;
x_25 = x_212;
goto block_72;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint64_t x_241; lean_object* x_242; lean_object* x_243; 
x_237 = lean_ctor_get(x_10, 1);
x_238 = lean_ctor_get(x_237, 1);
x_239 = lean_ctor_get(x_219, 0);
lean_inc(x_239);
lean_dec_ref(x_219);
x_240 = lean_ctor_get(x_238, 6);
x_241 = lean_unbox_uint64(x_239);
lean_dec(x_239);
lean_inc_ref(x_240);
x_242 = l_Lake_Cache_getArtifact_x3f(x_240, x_241, x_1, x_212);
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_dec(x_218);
lean_inc(x_216);
lean_inc_ref(x_215);
lean_inc_ref(x_213);
lean_dec_ref(x_10);
lean_dec(x_5);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 x_244 = x_11;
} else {
 lean_dec_ref(x_11);
 x_244 = lean_box(0);
}
x_245 = lean_ctor_get(x_242, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_246 = x_242;
} else {
 lean_dec_ref(x_242);
 x_246 = lean_box(0);
}
x_247 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__0;
x_248 = lean_uint64_to_nat(x_3);
x_249 = l_Nat_reprFast(x_248);
x_250 = lean_unsigned_to_nat(7u);
x_251 = lean_unsigned_to_nat(0u);
x_252 = lean_string_utf8_byte_size(x_249);
lean_inc_ref(x_249);
x_253 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_253, 0, x_249);
lean_ctor_set(x_253, 1, x_251);
lean_ctor_set(x_253, 2, x_252);
x_254 = l_Substring_nextn(x_253, x_250, x_251);
lean_dec_ref(x_253);
x_255 = lean_string_utf8_extract(x_249, x_251, x_254);
lean_dec(x_254);
lean_dec_ref(x_249);
x_256 = lean_string_append(x_247, x_255);
lean_dec_ref(x_255);
x_257 = l_Lake_resolveArtifactsUsing_x3f___redArg___closed__2;
x_258 = lean_string_append(x_256, x_257);
x_259 = 2;
x_260 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set_uint8(x_260, sizeof(void*)*1, x_259);
x_261 = lean_array_push(x_213, x_260);
if (lean_is_scalar(x_244)) {
 x_262 = lean_alloc_ctor(0, 3, 1);
} else {
 x_262 = x_244;
}
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_215);
lean_ctor_set(x_262, 2, x_216);
lean_ctor_set_uint8(x_262, sizeof(void*)*3, x_214);
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_243);
lean_ctor_set(x_263, 1, x_262);
if (lean_is_scalar(x_246)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_246;
}
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_245);
return x_264;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_242, 1);
lean_inc(x_265);
lean_dec_ref(x_242);
x_266 = l_Lake_SavedTrace_replayOrFetch(x_4, x_3, x_218, x_5, x_2, x_7, x_8, x_9, x_10, x_11, x_265);
lean_dec_ref(x_10);
lean_dec(x_5);
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_269 = x_266;
} else {
 lean_dec_ref(x_266);
 x_269 = lean_box(0);
}
x_270 = lean_ctor_get(x_267, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 x_271 = x_267;
} else {
 lean_dec_ref(x_267);
 x_271 = lean_box(0);
}
if (lean_is_scalar(x_271)) {
 x_272 = lean_alloc_ctor(0, 2, 0);
} else {
 x_272 = x_271;
}
lean_ctor_set(x_272, 0, x_243);
lean_ctor_set(x_272, 1, x_270);
if (lean_is_scalar(x_269)) {
 x_273 = lean_alloc_ctor(0, 2, 0);
} else {
 x_273 = x_269;
}
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_268);
return x_273;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec_ref(x_243);
x_274 = lean_ctor_get(x_266, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_275 = x_266;
} else {
 lean_dec_ref(x_266);
 x_275 = lean_box(0);
}
x_276 = lean_ctor_get(x_267, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_267, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 x_278 = x_267;
} else {
 lean_dec_ref(x_267);
 x_278 = lean_box(0);
}
if (lean_is_scalar(x_278)) {
 x_279 = lean_alloc_ctor(1, 2, 0);
} else {
 x_279 = x_278;
}
lean_ctor_set(x_279, 0, x_276);
lean_ctor_set(x_279, 1, x_277);
if (lean_is_scalar(x_275)) {
 x_280 = lean_alloc_ctor(0, 2, 0);
} else {
 x_280 = x_275;
}
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_274);
return x_280;
}
}
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
block_72:
{
if (lean_obj_tag(x_5) == 2)
{
lean_object* x_26; uint64_t x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_5, 0);
x_27 = lean_ctor_get_uint64(x_26, sizeof(void*)*3);
x_28 = lean_ctor_get(x_26, 1);
x_29 = lean_uint64_dec_eq(x_27, x_3);
if (x_29 == 0)
{
lean_dec_ref(x_23);
lean_dec_ref(x_5);
x_13 = x_24;
x_14 = x_25;
goto block_18;
}
else
{
if (lean_obj_tag(x_28) == 0)
{
lean_dec_ref(x_23);
lean_dec_ref(x_5);
x_13 = x_24;
x_14 = x_25;
goto block_18;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_inc(x_30);
x_31 = l_UInt64_fromJson_x3f(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_23);
lean_dec_ref(x_5);
x_13 = x_24;
x_14 = x_25;
goto block_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint64_t x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_23, 1);
x_33 = lean_ctor_get(x_32, 1);
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
lean_dec_ref(x_31);
x_35 = lean_ctor_get(x_33, 6);
x_36 = lean_unbox_uint64(x_34);
lean_dec(x_34);
lean_inc_ref(x_35);
x_37 = l_Lake_Cache_getArtifact_x3f(x_35, x_36, x_1, x_25);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
lean_dec(x_30);
lean_dec_ref(x_23);
lean_dec_ref(x_5);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec_ref(x_37);
x_13 = x_24;
x_14 = x_39;
goto block_18;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec_ref(x_37);
x_41 = lean_st_ref_take(x_6, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec_ref(x_41);
lean_inc(x_30);
x_44 = l_Lake_CacheMap_insertCore(x_3, x_30, x_42);
x_45 = lean_st_ref_set(x_6, x_44, x_43);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = l_Lake_SavedTrace_replayOrFetch(x_4, x_3, x_30, x_5, x_19, x_20, x_21, x_22, x_23, x_24, x_46);
lean_dec_ref(x_23);
lean_dec_ref(x_5);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_47);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_47, 0);
lean_dec(x_50);
x_51 = !lean_is_exclusive(x_48);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_48, 0);
lean_dec(x_52);
lean_ctor_set(x_48, 0, x_38);
return x_47;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
lean_dec(x_48);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_38);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_47, 0, x_54);
return x_47;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_47, 1);
lean_inc(x_55);
lean_dec(x_47);
x_56 = lean_ctor_get(x_48, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_57 = x_48;
} else {
 lean_dec_ref(x_48);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_38);
lean_ctor_set(x_58, 1, x_56);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_55);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec_ref(x_38);
x_60 = !lean_is_exclusive(x_47);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_47, 0);
lean_dec(x_61);
x_62 = !lean_is_exclusive(x_48);
if (x_62 == 0)
{
return x_47;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_48, 0);
x_64 = lean_ctor_get(x_48, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_48);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_47, 0, x_65);
return x_47;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = lean_ctor_get(x_47, 1);
lean_inc(x_66);
lean_dec(x_47);
x_67 = lean_ctor_get(x_48, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_48, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_69 = x_48;
} else {
 lean_dec_ref(x_48);
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
return x_71;
}
}
}
}
}
}
}
else
{
lean_dec_ref(x_23);
lean_dec(x_5);
x_13 = x_24;
x_14 = x_25;
goto block_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 1);
lean_dec(x_13);
lean_inc_ref(x_1);
x_14 = l_Lake_Artifact_trace(x_1);
lean_ctor_set(x_10, 1, x_14);
if (x_2 == 0)
{
lean_object* x_19; 
lean_dec_ref(x_3);
x_19 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_19);
lean_dec_ref(x_1);
x_15 = x_19;
goto block_18;
}
else
{
lean_dec_ref(x_1);
x_15 = x_3;
goto block_18;
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
x_22 = lean_ctor_get(x_10, 2);
lean_inc(x_22);
lean_inc(x_20);
lean_dec(x_10);
lean_inc_ref(x_1);
x_23 = l_Lake_Artifact_trace(x_1);
x_24 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_21);
if (x_2 == 0)
{
lean_object* x_29; 
lean_dec_ref(x_3);
x_29 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_29);
lean_dec_ref(x_1);
x_25 = x_29;
goto block_28;
}
else
{
lean_dec_ref(x_1);
x_25 = x_3;
goto block_28;
}
block_28:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_11);
return x_27;
}
}
}
}
static lean_object* _init_l_Lake_buildArtifactUnlessUpToDate___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("restored artifact from cache to: ", 33, 33);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_20; 
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
x_23 = l_Lake_buildFileUnlessUpToDate_x27___closed__0;
lean_inc_ref(x_1);
x_24 = lean_string_append(x_1, x_23);
lean_inc_ref(x_24);
x_25 = l_Lake_readTraceFile(x_24, x_21, x_13);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_30 = x_26;
} else {
 lean_dec_ref(x_26);
 x_30 = lean_box(0);
}
lean_inc_ref(x_22);
lean_ctor_set(x_12, 0, x_29);
if (lean_obj_tag(x_8) == 0)
{
lean_dec(x_30);
x_31 = x_7;
x_32 = x_8;
x_33 = x_9;
x_34 = x_10;
x_35 = x_11;
x_36 = x_12;
x_37 = x_27;
goto block_197;
}
else
{
lean_object* x_198; lean_object* x_199; 
x_198 = lean_ctor_get(x_8, 0);
x_199 = lean_ctor_get(x_198, 19);
if (lean_obj_tag(x_199) == 0)
{
lean_dec(x_30);
x_31 = x_7;
x_32 = x_8;
x_33 = x_9;
x_34 = x_10;
x_35 = x_11;
x_36 = x_12;
x_37 = x_27;
goto block_197;
}
else
{
lean_object* x_200; uint64_t x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_275; lean_object* x_276; 
x_200 = lean_ctor_get(x_199, 0);
x_201 = lean_ctor_get_uint64(x_22, sizeof(void*)*3);
x_202 = lean_ctor_get(x_22, 2);
lean_inc_ref(x_11);
lean_inc(x_28);
x_275 = l_Lake_resolveArtifactsUsing_x3f___at___Lake_buildArtifactUnlessUpToDate_spec__0(x_4, x_7, x_201, x_24, x_28, x_200, x_8, x_9, x_10, x_11, x_12, x_27);
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; 
x_277 = lean_ctor_get(x_276, 0);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; 
lean_inc(x_200);
x_278 = lean_ctor_get(x_275, 1);
lean_inc(x_278);
lean_dec_ref(x_275);
x_279 = lean_ctor_get(x_276, 1);
lean_inc(x_279);
lean_dec_ref(x_276);
x_280 = l_Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0___redArg(x_1, x_22, x_28, x_202, x_11, x_279, x_278);
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_281, 0);
x_283 = lean_unbox(x_282);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_284 = lean_ctor_get(x_280, 1);
lean_inc(x_284);
lean_dec_ref(x_280);
x_285 = lean_ctor_get(x_281, 1);
lean_inc(x_285);
lean_dec(x_281);
lean_inc_ref(x_11);
lean_inc_ref(x_1);
x_286 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_3, x_22, x_24, x_7, x_8, x_9, x_10, x_11, x_285, x_284);
lean_dec_ref(x_24);
lean_dec_ref(x_22);
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; lean_object* x_289; 
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec_ref(x_286);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
lean_dec_ref(x_287);
x_203 = x_11;
x_204 = x_289;
x_205 = x_288;
goto block_274;
}
else
{
uint8_t x_290; 
lean_dec(x_200);
lean_dec(x_30);
lean_dec_ref(x_11);
lean_dec_ref(x_1);
x_290 = !lean_is_exclusive(x_286);
if (x_290 == 0)
{
lean_object* x_291; uint8_t x_292; 
x_291 = lean_ctor_get(x_286, 0);
lean_dec(x_291);
x_292 = !lean_is_exclusive(x_287);
if (x_292 == 0)
{
return x_286;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_ctor_get(x_287, 0);
x_294 = lean_ctor_get(x_287, 1);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_287);
x_295 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_295, 0, x_293);
lean_ctor_set(x_295, 1, x_294);
lean_ctor_set(x_286, 0, x_295);
return x_286;
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_296 = lean_ctor_get(x_286, 1);
lean_inc(x_296);
lean_dec(x_286);
x_297 = lean_ctor_get(x_287, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_287, 1);
lean_inc(x_298);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 x_299 = x_287;
} else {
 lean_dec_ref(x_287);
 x_299 = lean_box(0);
}
if (lean_is_scalar(x_299)) {
 x_300 = lean_alloc_ctor(1, 2, 0);
} else {
 x_300 = x_299;
}
lean_ctor_set(x_300, 0, x_297);
lean_ctor_set(x_300, 1, x_298);
x_301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_296);
return x_301;
}
}
}
else
{
lean_object* x_302; lean_object* x_303; 
lean_dec_ref(x_24);
lean_dec_ref(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_302 = lean_ctor_get(x_280, 1);
lean_inc(x_302);
lean_dec_ref(x_280);
x_303 = lean_ctor_get(x_281, 1);
lean_inc(x_303);
lean_dec(x_281);
x_203 = x_11;
x_204 = x_303;
x_205 = x_302;
goto block_274;
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; 
lean_inc_ref(x_277);
lean_dec(x_30);
lean_dec(x_28);
lean_dec_ref(x_24);
lean_dec_ref(x_22);
lean_dec_ref(x_2);
x_304 = lean_ctor_get(x_275, 1);
lean_inc(x_304);
lean_dec_ref(x_275);
x_305 = lean_ctor_get(x_276, 1);
lean_inc(x_305);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_306 = x_276;
} else {
 lean_dec_ref(x_276);
 x_306 = lean_box(0);
}
x_307 = lean_ctor_get(x_277, 0);
lean_inc(x_307);
lean_dec_ref(x_277);
x_308 = l_System_FilePath_pathExists(x_1, x_304);
x_309 = !lean_is_exclusive(x_308);
if (x_309 == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; lean_object* x_314; lean_object* x_315; 
x_310 = lean_ctor_get(x_308, 0);
x_311 = lean_ctor_get(x_308, 1);
x_312 = lean_ctor_get(x_305, 0);
x_313 = lean_ctor_get_uint8(x_305, sizeof(void*)*3);
x_314 = lean_ctor_get(x_305, 1);
x_315 = lean_ctor_get(x_305, 2);
if (x_5 == 0)
{
lean_free_object(x_308);
lean_dec(x_310);
lean_dec(x_306);
goto block_318;
}
else
{
uint8_t x_319; 
x_319 = lean_unbox(x_310);
lean_dec(x_310);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; uint64_t x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_358; lean_object* x_359; uint8_t x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
lean_inc(x_315);
lean_inc_ref(x_314);
lean_inc_ref(x_312);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 lean_ctor_release(x_305, 1);
 lean_ctor_release(x_305, 2);
 x_320 = x_305;
} else {
 lean_dec_ref(x_305);
 x_320 = lean_box(0);
}
x_321 = lean_ctor_get(x_307, 0);
x_322 = lean_ctor_get_uint64(x_307, sizeof(void*)*3);
x_358 = l_Lake_buildArtifactUnlessUpToDate___closed__0;
x_359 = lean_string_append(x_358, x_1);
x_360 = 0;
x_361 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_361, 0, x_359);
lean_ctor_set_uint8(x_361, sizeof(void*)*1, x_360);
x_362 = lean_array_push(x_312, x_361);
x_363 = l_Lake_copyFile(x_321, x_1, x_311);
if (lean_obj_tag(x_363) == 0)
{
if (x_6 == 0)
{
lean_object* x_364; lean_object* x_365; 
lean_free_object(x_308);
x_364 = lean_ctor_get(x_363, 1);
lean_inc(x_364);
lean_dec_ref(x_363);
lean_inc(x_315);
lean_inc_ref(x_314);
lean_inc_ref(x_362);
x_365 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_365, 0, x_362);
lean_ctor_set(x_365, 1, x_314);
lean_ctor_set(x_365, 2, x_315);
lean_ctor_set_uint8(x_365, sizeof(void*)*3, x_313);
x_323 = x_7;
x_324 = x_8;
x_325 = x_9;
x_326 = x_10;
x_327 = x_11;
x_328 = x_365;
x_329 = x_362;
x_330 = x_313;
x_331 = x_314;
x_332 = x_315;
x_333 = x_364;
goto block_357;
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_366 = lean_ctor_get(x_363, 1);
lean_inc(x_366);
lean_dec_ref(x_363);
x_367 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_367, 0, x_5);
lean_ctor_set_uint8(x_367, 1, x_5);
lean_ctor_set_uint8(x_367, 2, x_5);
lean_inc_ref_n(x_367, 2);
x_368 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set(x_368, 1, x_367);
lean_ctor_set(x_368, 2, x_367);
x_369 = l_IO_setAccessRights(x_1, x_368, x_366);
lean_dec_ref(x_368);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_370; lean_object* x_371; 
lean_free_object(x_308);
x_370 = lean_ctor_get(x_369, 1);
lean_inc(x_370);
lean_dec_ref(x_369);
lean_inc(x_315);
lean_inc_ref(x_314);
lean_inc_ref(x_362);
x_371 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_371, 0, x_362);
lean_ctor_set(x_371, 1, x_314);
lean_ctor_set(x_371, 2, x_315);
lean_ctor_set_uint8(x_371, sizeof(void*)*3, x_313);
x_323 = x_7;
x_324 = x_8;
x_325 = x_9;
x_326 = x_10;
x_327 = x_11;
x_328 = x_371;
x_329 = x_362;
x_330 = x_313;
x_331 = x_314;
x_332 = x_315;
x_333 = x_370;
goto block_357;
}
else
{
uint8_t x_372; 
lean_dec(x_320);
lean_dec(x_307);
lean_dec(x_306);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_372 = !lean_is_exclusive(x_369);
if (x_372 == 0)
{
lean_object* x_373; lean_object* x_374; uint8_t x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_373 = lean_ctor_get(x_369, 0);
x_374 = lean_io_error_to_string(x_373);
x_375 = 3;
x_376 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_376, 0, x_374);
lean_ctor_set_uint8(x_376, sizeof(void*)*1, x_375);
x_377 = lean_array_get_size(x_362);
x_378 = lean_array_push(x_362, x_376);
x_379 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_379, 0, x_378);
lean_ctor_set(x_379, 1, x_314);
lean_ctor_set(x_379, 2, x_315);
lean_ctor_set_uint8(x_379, sizeof(void*)*3, x_313);
lean_ctor_set_tag(x_308, 1);
lean_ctor_set(x_308, 1, x_379);
lean_ctor_set(x_308, 0, x_377);
lean_ctor_set_tag(x_369, 0);
lean_ctor_set(x_369, 0, x_308);
return x_369;
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; uint8_t x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_380 = lean_ctor_get(x_369, 0);
x_381 = lean_ctor_get(x_369, 1);
lean_inc(x_381);
lean_inc(x_380);
lean_dec(x_369);
x_382 = lean_io_error_to_string(x_380);
x_383 = 3;
x_384 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_384, 0, x_382);
lean_ctor_set_uint8(x_384, sizeof(void*)*1, x_383);
x_385 = lean_array_get_size(x_362);
x_386 = lean_array_push(x_362, x_384);
x_387 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_387, 0, x_386);
lean_ctor_set(x_387, 1, x_314);
lean_ctor_set(x_387, 2, x_315);
lean_ctor_set_uint8(x_387, sizeof(void*)*3, x_313);
lean_ctor_set_tag(x_308, 1);
lean_ctor_set(x_308, 1, x_387);
lean_ctor_set(x_308, 0, x_385);
x_388 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_388, 0, x_308);
lean_ctor_set(x_388, 1, x_381);
return x_388;
}
}
}
}
else
{
uint8_t x_389; 
lean_dec(x_320);
lean_dec(x_307);
lean_dec(x_306);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_389 = !lean_is_exclusive(x_363);
if (x_389 == 0)
{
lean_object* x_390; lean_object* x_391; uint8_t x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_390 = lean_ctor_get(x_363, 0);
x_391 = lean_io_error_to_string(x_390);
x_392 = 3;
x_393 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_393, 0, x_391);
lean_ctor_set_uint8(x_393, sizeof(void*)*1, x_392);
x_394 = lean_array_get_size(x_362);
x_395 = lean_array_push(x_362, x_393);
x_396 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_396, 0, x_395);
lean_ctor_set(x_396, 1, x_314);
lean_ctor_set(x_396, 2, x_315);
lean_ctor_set_uint8(x_396, sizeof(void*)*3, x_313);
lean_ctor_set_tag(x_308, 1);
lean_ctor_set(x_308, 1, x_396);
lean_ctor_set(x_308, 0, x_394);
lean_ctor_set_tag(x_363, 0);
lean_ctor_set(x_363, 0, x_308);
return x_363;
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; uint8_t x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_397 = lean_ctor_get(x_363, 0);
x_398 = lean_ctor_get(x_363, 1);
lean_inc(x_398);
lean_inc(x_397);
lean_dec(x_363);
x_399 = lean_io_error_to_string(x_397);
x_400 = 3;
x_401 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_401, 0, x_399);
lean_ctor_set_uint8(x_401, sizeof(void*)*1, x_400);
x_402 = lean_array_get_size(x_362);
x_403 = lean_array_push(x_362, x_401);
x_404 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_404, 0, x_403);
lean_ctor_set(x_404, 1, x_314);
lean_ctor_set(x_404, 2, x_315);
lean_ctor_set_uint8(x_404, sizeof(void*)*3, x_313);
lean_ctor_set_tag(x_308, 1);
lean_ctor_set(x_308, 1, x_404);
lean_ctor_set(x_308, 0, x_402);
x_405 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_405, 0, x_308);
lean_ctor_set(x_405, 1, x_398);
return x_405;
}
}
block_357:
{
lean_object* x_334; 
lean_inc_ref(x_1);
x_334 = l_Lake_writeFileHash(x_1, x_322, x_333);
if (lean_obj_tag(x_334) == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; 
lean_dec(x_332);
lean_dec_ref(x_331);
lean_dec_ref(x_329);
lean_dec(x_320);
lean_dec(x_306);
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_334, 1);
lean_inc(x_336);
lean_dec_ref(x_334);
x_337 = l_Lake_buildArtifactUnlessUpToDate___lam__0(x_307, x_5, x_1, x_335, x_323, x_324, x_325, x_326, x_327, x_328, x_336);
lean_dec_ref(x_327);
lean_dec(x_326);
lean_dec(x_325);
lean_dec(x_324);
lean_dec_ref(x_323);
return x_337;
}
else
{
uint8_t x_338; 
lean_dec_ref(x_328);
lean_dec_ref(x_327);
lean_dec(x_326);
lean_dec(x_325);
lean_dec(x_324);
lean_dec_ref(x_323);
lean_dec(x_307);
lean_dec_ref(x_1);
x_338 = !lean_is_exclusive(x_334);
if (x_338 == 0)
{
lean_object* x_339; lean_object* x_340; uint8_t x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_339 = lean_ctor_get(x_334, 0);
x_340 = lean_io_error_to_string(x_339);
x_341 = 3;
x_342 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_342, 0, x_340);
lean_ctor_set_uint8(x_342, sizeof(void*)*1, x_341);
x_343 = lean_array_get_size(x_329);
x_344 = lean_array_push(x_329, x_342);
if (lean_is_scalar(x_320)) {
 x_345 = lean_alloc_ctor(0, 3, 1);
} else {
 x_345 = x_320;
}
lean_ctor_set(x_345, 0, x_344);
lean_ctor_set(x_345, 1, x_331);
lean_ctor_set(x_345, 2, x_332);
lean_ctor_set_uint8(x_345, sizeof(void*)*3, x_330);
if (lean_is_scalar(x_306)) {
 x_346 = lean_alloc_ctor(1, 2, 0);
} else {
 x_346 = x_306;
 lean_ctor_set_tag(x_346, 1);
}
lean_ctor_set(x_346, 0, x_343);
lean_ctor_set(x_346, 1, x_345);
lean_ctor_set_tag(x_334, 0);
lean_ctor_set(x_334, 0, x_346);
return x_334;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; uint8_t x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_347 = lean_ctor_get(x_334, 0);
x_348 = lean_ctor_get(x_334, 1);
lean_inc(x_348);
lean_inc(x_347);
lean_dec(x_334);
x_349 = lean_io_error_to_string(x_347);
x_350 = 3;
x_351 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_351, 0, x_349);
lean_ctor_set_uint8(x_351, sizeof(void*)*1, x_350);
x_352 = lean_array_get_size(x_329);
x_353 = lean_array_push(x_329, x_351);
if (lean_is_scalar(x_320)) {
 x_354 = lean_alloc_ctor(0, 3, 1);
} else {
 x_354 = x_320;
}
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_331);
lean_ctor_set(x_354, 2, x_332);
lean_ctor_set_uint8(x_354, sizeof(void*)*3, x_330);
if (lean_is_scalar(x_306)) {
 x_355 = lean_alloc_ctor(1, 2, 0);
} else {
 x_355 = x_306;
 lean_ctor_set_tag(x_355, 1);
}
lean_ctor_set(x_355, 0, x_352);
lean_ctor_set(x_355, 1, x_354);
x_356 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_348);
return x_356;
}
}
}
}
else
{
lean_free_object(x_308);
lean_dec(x_306);
goto block_318;
}
}
block_318:
{
lean_object* x_316; lean_object* x_317; 
x_316 = lean_box(0);
x_317 = l_Lake_buildArtifactUnlessUpToDate___lam__0(x_307, x_5, x_1, x_316, x_7, x_8, x_9, x_10, x_11, x_305, x_311);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
return x_317;
}
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; uint8_t x_409; lean_object* x_410; lean_object* x_411; 
x_406 = lean_ctor_get(x_308, 0);
x_407 = lean_ctor_get(x_308, 1);
lean_inc(x_407);
lean_inc(x_406);
lean_dec(x_308);
x_408 = lean_ctor_get(x_305, 0);
x_409 = lean_ctor_get_uint8(x_305, sizeof(void*)*3);
x_410 = lean_ctor_get(x_305, 1);
x_411 = lean_ctor_get(x_305, 2);
if (x_5 == 0)
{
lean_dec(x_406);
lean_dec(x_306);
goto block_414;
}
else
{
uint8_t x_415; 
x_415 = lean_unbox(x_406);
lean_dec(x_406);
if (x_415 == 0)
{
lean_object* x_416; lean_object* x_417; uint64_t x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; uint8_t x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_446; lean_object* x_447; uint8_t x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
lean_inc(x_411);
lean_inc_ref(x_410);
lean_inc_ref(x_408);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 lean_ctor_release(x_305, 1);
 lean_ctor_release(x_305, 2);
 x_416 = x_305;
} else {
 lean_dec_ref(x_305);
 x_416 = lean_box(0);
}
x_417 = lean_ctor_get(x_307, 0);
x_418 = lean_ctor_get_uint64(x_307, sizeof(void*)*3);
x_446 = l_Lake_buildArtifactUnlessUpToDate___closed__0;
x_447 = lean_string_append(x_446, x_1);
x_448 = 0;
x_449 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_449, 0, x_447);
lean_ctor_set_uint8(x_449, sizeof(void*)*1, x_448);
x_450 = lean_array_push(x_408, x_449);
x_451 = l_Lake_copyFile(x_417, x_1, x_407);
if (lean_obj_tag(x_451) == 0)
{
if (x_6 == 0)
{
lean_object* x_452; lean_object* x_453; 
x_452 = lean_ctor_get(x_451, 1);
lean_inc(x_452);
lean_dec_ref(x_451);
lean_inc(x_411);
lean_inc_ref(x_410);
lean_inc_ref(x_450);
x_453 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_453, 0, x_450);
lean_ctor_set(x_453, 1, x_410);
lean_ctor_set(x_453, 2, x_411);
lean_ctor_set_uint8(x_453, sizeof(void*)*3, x_409);
x_419 = x_7;
x_420 = x_8;
x_421 = x_9;
x_422 = x_10;
x_423 = x_11;
x_424 = x_453;
x_425 = x_450;
x_426 = x_409;
x_427 = x_410;
x_428 = x_411;
x_429 = x_452;
goto block_445;
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_454 = lean_ctor_get(x_451, 1);
lean_inc(x_454);
lean_dec_ref(x_451);
x_455 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_455, 0, x_5);
lean_ctor_set_uint8(x_455, 1, x_5);
lean_ctor_set_uint8(x_455, 2, x_5);
lean_inc_ref_n(x_455, 2);
x_456 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_456, 0, x_455);
lean_ctor_set(x_456, 1, x_455);
lean_ctor_set(x_456, 2, x_455);
x_457 = l_IO_setAccessRights(x_1, x_456, x_454);
lean_dec_ref(x_456);
if (lean_obj_tag(x_457) == 0)
{
lean_object* x_458; lean_object* x_459; 
x_458 = lean_ctor_get(x_457, 1);
lean_inc(x_458);
lean_dec_ref(x_457);
lean_inc(x_411);
lean_inc_ref(x_410);
lean_inc_ref(x_450);
x_459 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_459, 0, x_450);
lean_ctor_set(x_459, 1, x_410);
lean_ctor_set(x_459, 2, x_411);
lean_ctor_set_uint8(x_459, sizeof(void*)*3, x_409);
x_419 = x_7;
x_420 = x_8;
x_421 = x_9;
x_422 = x_10;
x_423 = x_11;
x_424 = x_459;
x_425 = x_450;
x_426 = x_409;
x_427 = x_410;
x_428 = x_411;
x_429 = x_458;
goto block_445;
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; uint8_t x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
lean_dec(x_416);
lean_dec(x_307);
lean_dec(x_306);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_460 = lean_ctor_get(x_457, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_457, 1);
lean_inc(x_461);
if (lean_is_exclusive(x_457)) {
 lean_ctor_release(x_457, 0);
 lean_ctor_release(x_457, 1);
 x_462 = x_457;
} else {
 lean_dec_ref(x_457);
 x_462 = lean_box(0);
}
x_463 = lean_io_error_to_string(x_460);
x_464 = 3;
x_465 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_465, 0, x_463);
lean_ctor_set_uint8(x_465, sizeof(void*)*1, x_464);
x_466 = lean_array_get_size(x_450);
x_467 = lean_array_push(x_450, x_465);
x_468 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_468, 0, x_467);
lean_ctor_set(x_468, 1, x_410);
lean_ctor_set(x_468, 2, x_411);
lean_ctor_set_uint8(x_468, sizeof(void*)*3, x_409);
x_469 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_469, 0, x_466);
lean_ctor_set(x_469, 1, x_468);
if (lean_is_scalar(x_462)) {
 x_470 = lean_alloc_ctor(0, 2, 0);
} else {
 x_470 = x_462;
 lean_ctor_set_tag(x_470, 0);
}
lean_ctor_set(x_470, 0, x_469);
lean_ctor_set(x_470, 1, x_461);
return x_470;
}
}
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; uint8_t x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
lean_dec(x_416);
lean_dec(x_307);
lean_dec(x_306);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_471 = lean_ctor_get(x_451, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_451, 1);
lean_inc(x_472);
if (lean_is_exclusive(x_451)) {
 lean_ctor_release(x_451, 0);
 lean_ctor_release(x_451, 1);
 x_473 = x_451;
} else {
 lean_dec_ref(x_451);
 x_473 = lean_box(0);
}
x_474 = lean_io_error_to_string(x_471);
x_475 = 3;
x_476 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_476, 0, x_474);
lean_ctor_set_uint8(x_476, sizeof(void*)*1, x_475);
x_477 = lean_array_get_size(x_450);
x_478 = lean_array_push(x_450, x_476);
x_479 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_479, 0, x_478);
lean_ctor_set(x_479, 1, x_410);
lean_ctor_set(x_479, 2, x_411);
lean_ctor_set_uint8(x_479, sizeof(void*)*3, x_409);
x_480 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_480, 0, x_477);
lean_ctor_set(x_480, 1, x_479);
if (lean_is_scalar(x_473)) {
 x_481 = lean_alloc_ctor(0, 2, 0);
} else {
 x_481 = x_473;
 lean_ctor_set_tag(x_481, 0);
}
lean_ctor_set(x_481, 0, x_480);
lean_ctor_set(x_481, 1, x_472);
return x_481;
}
block_445:
{
lean_object* x_430; 
lean_inc_ref(x_1);
x_430 = l_Lake_writeFileHash(x_1, x_418, x_429);
if (lean_obj_tag(x_430) == 0)
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; 
lean_dec(x_428);
lean_dec_ref(x_427);
lean_dec_ref(x_425);
lean_dec(x_416);
lean_dec(x_306);
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_430, 1);
lean_inc(x_432);
lean_dec_ref(x_430);
x_433 = l_Lake_buildArtifactUnlessUpToDate___lam__0(x_307, x_5, x_1, x_431, x_419, x_420, x_421, x_422, x_423, x_424, x_432);
lean_dec_ref(x_423);
lean_dec(x_422);
lean_dec(x_421);
lean_dec(x_420);
lean_dec_ref(x_419);
return x_433;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; 
lean_dec_ref(x_424);
lean_dec_ref(x_423);
lean_dec(x_422);
lean_dec(x_421);
lean_dec(x_420);
lean_dec_ref(x_419);
lean_dec(x_307);
lean_dec_ref(x_1);
x_434 = lean_ctor_get(x_430, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_430, 1);
lean_inc(x_435);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 x_436 = x_430;
} else {
 lean_dec_ref(x_430);
 x_436 = lean_box(0);
}
x_437 = lean_io_error_to_string(x_434);
x_438 = 3;
x_439 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_439, 0, x_437);
lean_ctor_set_uint8(x_439, sizeof(void*)*1, x_438);
x_440 = lean_array_get_size(x_425);
x_441 = lean_array_push(x_425, x_439);
if (lean_is_scalar(x_416)) {
 x_442 = lean_alloc_ctor(0, 3, 1);
} else {
 x_442 = x_416;
}
lean_ctor_set(x_442, 0, x_441);
lean_ctor_set(x_442, 1, x_427);
lean_ctor_set(x_442, 2, x_428);
lean_ctor_set_uint8(x_442, sizeof(void*)*3, x_426);
if (lean_is_scalar(x_306)) {
 x_443 = lean_alloc_ctor(1, 2, 0);
} else {
 x_443 = x_306;
 lean_ctor_set_tag(x_443, 1);
}
lean_ctor_set(x_443, 0, x_440);
lean_ctor_set(x_443, 1, x_442);
if (lean_is_scalar(x_436)) {
 x_444 = lean_alloc_ctor(0, 2, 0);
} else {
 x_444 = x_436;
 lean_ctor_set_tag(x_444, 0);
}
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_435);
return x_444;
}
}
}
else
{
lean_dec(x_306);
goto block_414;
}
}
block_414:
{
lean_object* x_412; lean_object* x_413; 
x_412 = lean_box(0);
x_413 = l_Lake_buildArtifactUnlessUpToDate___lam__0(x_307, x_5, x_1, x_412, x_7, x_8, x_9, x_10, x_11, x_305, x_407);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
return x_413;
}
}
}
}
else
{
uint8_t x_482; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec_ref(x_24);
lean_dec_ref(x_22);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_482 = !lean_is_exclusive(x_275);
if (x_482 == 0)
{
lean_object* x_483; uint8_t x_484; 
x_483 = lean_ctor_get(x_275, 0);
lean_dec(x_483);
x_484 = !lean_is_exclusive(x_276);
if (x_484 == 0)
{
return x_275;
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; 
x_485 = lean_ctor_get(x_276, 0);
x_486 = lean_ctor_get(x_276, 1);
lean_inc(x_486);
lean_inc(x_485);
lean_dec(x_276);
x_487 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_487, 0, x_485);
lean_ctor_set(x_487, 1, x_486);
lean_ctor_set(x_275, 0, x_487);
return x_275;
}
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_488 = lean_ctor_get(x_275, 1);
lean_inc(x_488);
lean_dec(x_275);
x_489 = lean_ctor_get(x_276, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_276, 1);
lean_inc(x_490);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_491 = x_276;
} else {
 lean_dec_ref(x_276);
 x_491 = lean_box(0);
}
if (lean_is_scalar(x_491)) {
 x_492 = lean_alloc_ctor(1, 2, 0);
} else {
 x_492 = x_491;
}
lean_ctor_set(x_492, 0, x_489);
lean_ctor_set(x_492, 1, x_490);
x_493 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_493, 0, x_492);
lean_ctor_set(x_493, 1, x_488);
return x_493;
}
}
block_274:
{
lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_206 = lean_ctor_get(x_203, 1);
lean_inc(x_206);
lean_dec_ref(x_203);
x_207 = lean_ctor_get(x_206, 1);
lean_inc_ref(x_207);
lean_dec(x_206);
x_208 = !lean_is_exclusive(x_204);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_209 = lean_ctor_get(x_204, 0);
x_210 = lean_ctor_get(x_204, 1);
x_211 = lean_ctor_get(x_207, 6);
lean_inc_ref(x_211);
lean_dec_ref(x_207);
lean_inc_ref(x_1);
x_212 = l_Lake_Cache_saveArtifact(x_211, x_1, x_4, x_3, x_6, x_205);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint64_t x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
lean_dec_ref(x_210);
lean_dec(x_30);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec_ref(x_212);
x_215 = lean_st_ref_take(x_200, x_214);
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec_ref(x_215);
x_218 = lean_ctor_get(x_213, 0);
lean_inc_ref(x_218);
x_219 = lean_ctor_get_uint64(x_213, sizeof(void*)*3);
x_220 = lean_uint64_to_nat(x_219);
x_221 = l_Lean_bignumToJson(x_220);
x_222 = l_Lake_CacheMap_insertCore(x_201, x_221, x_216);
x_223 = lean_st_ref_set(x_200, x_222, x_217);
lean_dec(x_200);
x_224 = lean_ctor_get(x_223, 1);
lean_inc(x_224);
lean_dec_ref(x_223);
x_225 = l_Lake_Artifact_trace(x_213);
lean_ctor_set(x_204, 1, x_225);
if (x_5 == 0)
{
lean_dec_ref(x_1);
x_14 = x_204;
x_15 = x_224;
x_16 = x_218;
goto block_19;
}
else
{
lean_dec_ref(x_218);
x_14 = x_204;
x_15 = x_224;
x_16 = x_1;
goto block_19;
}
}
else
{
uint8_t x_226; 
lean_dec(x_200);
lean_dec_ref(x_1);
x_226 = !lean_is_exclusive(x_212);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; uint8_t x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_227 = lean_ctor_get(x_212, 0);
x_228 = lean_io_error_to_string(x_227);
x_229 = 3;
x_230 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set_uint8(x_230, sizeof(void*)*1, x_229);
x_231 = lean_array_get_size(x_209);
x_232 = lean_array_push(x_209, x_230);
lean_ctor_set(x_204, 0, x_232);
if (lean_is_scalar(x_30)) {
 x_233 = lean_alloc_ctor(1, 2, 0);
} else {
 x_233 = x_30;
 lean_ctor_set_tag(x_233, 1);
}
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_204);
lean_ctor_set_tag(x_212, 0);
lean_ctor_set(x_212, 0, x_233);
return x_212;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_234 = lean_ctor_get(x_212, 0);
x_235 = lean_ctor_get(x_212, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_212);
x_236 = lean_io_error_to_string(x_234);
x_237 = 3;
x_238 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set_uint8(x_238, sizeof(void*)*1, x_237);
x_239 = lean_array_get_size(x_209);
x_240 = lean_array_push(x_209, x_238);
lean_ctor_set(x_204, 0, x_240);
if (lean_is_scalar(x_30)) {
 x_241 = lean_alloc_ctor(1, 2, 0);
} else {
 x_241 = x_30;
 lean_ctor_set_tag(x_241, 1);
}
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_204);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_235);
return x_242;
}
}
}
else
{
lean_object* x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_243 = lean_ctor_get(x_204, 0);
x_244 = lean_ctor_get_uint8(x_204, sizeof(void*)*3);
x_245 = lean_ctor_get(x_204, 1);
x_246 = lean_ctor_get(x_204, 2);
lean_inc(x_246);
lean_inc(x_245);
lean_inc(x_243);
lean_dec(x_204);
x_247 = lean_ctor_get(x_207, 6);
lean_inc_ref(x_247);
lean_dec_ref(x_207);
lean_inc_ref(x_1);
x_248 = l_Lake_Cache_saveArtifact(x_247, x_1, x_4, x_3, x_6, x_205);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint64_t x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec_ref(x_245);
lean_dec(x_30);
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec_ref(x_248);
x_251 = lean_st_ref_take(x_200, x_250);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec_ref(x_251);
x_254 = lean_ctor_get(x_249, 0);
lean_inc_ref(x_254);
x_255 = lean_ctor_get_uint64(x_249, sizeof(void*)*3);
x_256 = lean_uint64_to_nat(x_255);
x_257 = l_Lean_bignumToJson(x_256);
x_258 = l_Lake_CacheMap_insertCore(x_201, x_257, x_252);
x_259 = lean_st_ref_set(x_200, x_258, x_253);
lean_dec(x_200);
x_260 = lean_ctor_get(x_259, 1);
lean_inc(x_260);
lean_dec_ref(x_259);
x_261 = l_Lake_Artifact_trace(x_249);
x_262 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_262, 0, x_243);
lean_ctor_set(x_262, 1, x_261);
lean_ctor_set(x_262, 2, x_246);
lean_ctor_set_uint8(x_262, sizeof(void*)*3, x_244);
if (x_5 == 0)
{
lean_dec_ref(x_1);
x_14 = x_262;
x_15 = x_260;
x_16 = x_254;
goto block_19;
}
else
{
lean_dec_ref(x_254);
x_14 = x_262;
x_15 = x_260;
x_16 = x_1;
goto block_19;
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_200);
lean_dec_ref(x_1);
x_263 = lean_ctor_get(x_248, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_248, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_265 = x_248;
} else {
 lean_dec_ref(x_248);
 x_265 = lean_box(0);
}
x_266 = lean_io_error_to_string(x_263);
x_267 = 3;
x_268 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_268, 0, x_266);
lean_ctor_set_uint8(x_268, sizeof(void*)*1, x_267);
x_269 = lean_array_get_size(x_243);
x_270 = lean_array_push(x_243, x_268);
x_271 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_245);
lean_ctor_set(x_271, 2, x_246);
lean_ctor_set_uint8(x_271, sizeof(void*)*3, x_244);
if (lean_is_scalar(x_30)) {
 x_272 = lean_alloc_ctor(1, 2, 0);
} else {
 x_272 = x_30;
 lean_ctor_set_tag(x_272, 1);
}
lean_ctor_set(x_272, 0, x_269);
lean_ctor_set(x_272, 1, x_271);
if (lean_is_scalar(x_265)) {
 x_273 = lean_alloc_ctor(0, 2, 0);
} else {
 x_273 = x_265;
 lean_ctor_set_tag(x_273, 0);
}
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_264);
return x_273;
}
}
}
}
}
block_197:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_38 = lean_ctor_get(x_22, 2);
x_39 = l_Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0___redArg(x_1, x_22, x_28, x_38, x_35, x_36, x_37);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 0);
x_42 = lean_unbox(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec_ref(x_39);
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
lean_inc_ref(x_1);
x_45 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_3, x_22, x_24, x_31, x_32, x_33, x_34, x_35, x_44, x_43);
lean_dec_ref(x_24);
lean_dec_ref(x_22);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec_ref(x_45);
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_46, 0);
x_51 = lean_ctor_get(x_46, 1);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_47);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; uint64_t x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_47, 0);
x_54 = lean_ctor_get(x_47, 1);
x_55 = lean_unbox_uint64(x_50);
lean_inc_ref(x_1);
x_56 = l_Lake_writeFileHash(x_1, x_55, x_48);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; uint64_t x_58; lean_object* x_59; uint8_t x_60; 
lean_dec_ref(x_54);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec_ref(x_56);
x_58 = lean_unbox_uint64(x_50);
lean_dec(x_50);
lean_inc_ref(x_1);
x_59 = l_Lake_computeArtifactTrace(x_1, x_1, x_58, x_57);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_59, 0);
lean_ctor_set(x_47, 1, x_61);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_59, 0, x_46);
return x_59;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_59, 0);
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_59);
lean_ctor_set(x_47, 1, x_62);
lean_ctor_set(x_46, 0, x_1);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_46);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_50);
lean_dec_ref(x_1);
x_65 = !lean_is_exclusive(x_56);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = lean_ctor_get(x_56, 0);
x_67 = lean_io_error_to_string(x_66);
x_68 = 3;
x_69 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set_uint8(x_69, sizeof(void*)*1, x_68);
x_70 = lean_array_get_size(x_53);
x_71 = lean_array_push(x_53, x_69);
lean_ctor_set(x_47, 0, x_71);
lean_ctor_set_tag(x_46, 1);
lean_ctor_set(x_46, 0, x_70);
lean_ctor_set_tag(x_56, 0);
lean_ctor_set(x_56, 0, x_46);
return x_56;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_72 = lean_ctor_get(x_56, 0);
x_73 = lean_ctor_get(x_56, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_56);
x_74 = lean_io_error_to_string(x_72);
x_75 = 3;
x_76 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*1, x_75);
x_77 = lean_array_get_size(x_53);
x_78 = lean_array_push(x_53, x_76);
lean_ctor_set(x_47, 0, x_78);
lean_ctor_set_tag(x_46, 1);
lean_ctor_set(x_46, 0, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_46);
lean_ctor_set(x_79, 1, x_73);
return x_79;
}
}
}
else
{
lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; uint64_t x_84; lean_object* x_85; 
x_80 = lean_ctor_get(x_47, 0);
x_81 = lean_ctor_get_uint8(x_47, sizeof(void*)*3);
x_82 = lean_ctor_get(x_47, 1);
x_83 = lean_ctor_get(x_47, 2);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_80);
lean_dec(x_47);
x_84 = lean_unbox_uint64(x_50);
lean_inc_ref(x_1);
x_85 = l_Lake_writeFileHash(x_1, x_84, x_48);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; uint64_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec_ref(x_82);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec_ref(x_85);
x_87 = lean_unbox_uint64(x_50);
lean_dec(x_50);
lean_inc_ref(x_1);
x_88 = l_Lake_computeArtifactTrace(x_1, x_1, x_87, x_86);
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
x_92 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_92, 0, x_80);
lean_ctor_set(x_92, 1, x_89);
lean_ctor_set(x_92, 2, x_83);
lean_ctor_set_uint8(x_92, sizeof(void*)*3, x_81);
lean_ctor_set(x_46, 1, x_92);
lean_ctor_set(x_46, 0, x_1);
if (lean_is_scalar(x_91)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_91;
}
lean_ctor_set(x_93, 0, x_46);
lean_ctor_set(x_93, 1, x_90);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_50);
lean_dec_ref(x_1);
x_94 = lean_ctor_get(x_85, 0);
lean_inc(x_94);
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
x_97 = lean_io_error_to_string(x_94);
x_98 = 3;
x_99 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set_uint8(x_99, sizeof(void*)*1, x_98);
x_100 = lean_array_get_size(x_80);
x_101 = lean_array_push(x_80, x_99);
x_102 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_82);
lean_ctor_set(x_102, 2, x_83);
lean_ctor_set_uint8(x_102, sizeof(void*)*3, x_81);
lean_ctor_set_tag(x_46, 1);
lean_ctor_set(x_46, 1, x_102);
lean_ctor_set(x_46, 0, x_100);
if (lean_is_scalar(x_96)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_96;
 lean_ctor_set_tag(x_103, 0);
}
lean_ctor_set(x_103, 0, x_46);
lean_ctor_set(x_103, 1, x_95);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint64_t x_110; lean_object* x_111; 
x_104 = lean_ctor_get(x_46, 0);
lean_inc(x_104);
lean_dec(x_46);
x_105 = lean_ctor_get(x_47, 0);
lean_inc_ref(x_105);
x_106 = lean_ctor_get_uint8(x_47, sizeof(void*)*3);
x_107 = lean_ctor_get(x_47, 1);
lean_inc_ref(x_107);
x_108 = lean_ctor_get(x_47, 2);
lean_inc(x_108);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 x_109 = x_47;
} else {
 lean_dec_ref(x_47);
 x_109 = lean_box(0);
}
x_110 = lean_unbox_uint64(x_104);
lean_inc_ref(x_1);
x_111 = l_Lake_writeFileHash(x_1, x_110, x_48);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; uint64_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec_ref(x_107);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec_ref(x_111);
x_113 = lean_unbox_uint64(x_104);
lean_dec(x_104);
lean_inc_ref(x_1);
x_114 = l_Lake_computeArtifactTrace(x_1, x_1, x_113, x_112);
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
if (lean_is_scalar(x_109)) {
 x_118 = lean_alloc_ctor(0, 3, 1);
} else {
 x_118 = x_109;
}
lean_ctor_set(x_118, 0, x_105);
lean_ctor_set(x_118, 1, x_115);
lean_ctor_set(x_118, 2, x_108);
lean_ctor_set_uint8(x_118, sizeof(void*)*3, x_106);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_1);
lean_ctor_set(x_119, 1, x_118);
if (lean_is_scalar(x_117)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_117;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_116);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_104);
lean_dec_ref(x_1);
x_121 = lean_ctor_get(x_111, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_111, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_123 = x_111;
} else {
 lean_dec_ref(x_111);
 x_123 = lean_box(0);
}
x_124 = lean_io_error_to_string(x_121);
x_125 = 3;
x_126 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set_uint8(x_126, sizeof(void*)*1, x_125);
x_127 = lean_array_get_size(x_105);
x_128 = lean_array_push(x_105, x_126);
if (lean_is_scalar(x_109)) {
 x_129 = lean_alloc_ctor(0, 3, 1);
} else {
 x_129 = x_109;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_107);
lean_ctor_set(x_129, 2, x_108);
lean_ctor_set_uint8(x_129, sizeof(void*)*3, x_106);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_129);
if (lean_is_scalar(x_123)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_123;
 lean_ctor_set_tag(x_131, 0);
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_122);
return x_131;
}
}
}
else
{
uint8_t x_132; 
lean_dec_ref(x_1);
x_132 = !lean_is_exclusive(x_45);
if (x_132 == 0)
{
lean_object* x_133; uint8_t x_134; 
x_133 = lean_ctor_get(x_45, 0);
lean_dec(x_133);
x_134 = !lean_is_exclusive(x_46);
if (x_134 == 0)
{
return x_45;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_46, 0);
x_136 = lean_ctor_get(x_46, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_46);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
lean_ctor_set(x_45, 0, x_137);
return x_45;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_138 = lean_ctor_get(x_45, 1);
lean_inc(x_138);
lean_dec(x_45);
x_139 = lean_ctor_get(x_46, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_46, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_141 = x_46;
} else {
 lean_dec_ref(x_46);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_138);
return x_143;
}
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec_ref(x_24);
lean_dec_ref(x_22);
lean_dec_ref(x_2);
x_144 = lean_ctor_get(x_39, 1);
lean_inc(x_144);
lean_dec_ref(x_39);
x_145 = lean_ctor_get(x_40, 1);
lean_inc(x_145);
lean_dec(x_40);
lean_inc_ref(x_1);
x_146 = l_Lake_fetchFileHash___redArg(x_1, x_3, x_35, x_145, x_144);
lean_dec_ref(x_35);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; uint8_t x_149; 
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec_ref(x_146);
x_149 = !lean_is_exclusive(x_147);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; uint64_t x_152; lean_object* x_153; uint8_t x_154; 
x_150 = lean_ctor_get(x_147, 0);
x_151 = lean_ctor_get(x_147, 1);
x_152 = lean_unbox_uint64(x_150);
lean_dec(x_150);
lean_inc_ref(x_1);
x_153 = l_Lake_computeArtifactTrace(x_1, x_1, x_152, x_148);
x_154 = !lean_is_exclusive(x_153);
if (x_154 == 0)
{
uint8_t x_155; 
x_155 = !lean_is_exclusive(x_151);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_153, 0);
x_157 = lean_ctor_get(x_151, 1);
lean_dec(x_157);
lean_ctor_set(x_151, 1, x_156);
lean_ctor_set(x_147, 0, x_1);
lean_ctor_set(x_153, 0, x_147);
return x_153;
}
else
{
lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; lean_object* x_162; 
x_158 = lean_ctor_get(x_153, 0);
x_159 = lean_ctor_get(x_151, 0);
x_160 = lean_ctor_get_uint8(x_151, sizeof(void*)*3);
x_161 = lean_ctor_get(x_151, 2);
lean_inc(x_161);
lean_inc(x_159);
lean_dec(x_151);
x_162 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_158);
lean_ctor_set(x_162, 2, x_161);
lean_ctor_set_uint8(x_162, sizeof(void*)*3, x_160);
lean_ctor_set(x_147, 1, x_162);
lean_ctor_set(x_147, 0, x_1);
lean_ctor_set(x_153, 0, x_147);
return x_153;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_163 = lean_ctor_get(x_153, 0);
x_164 = lean_ctor_get(x_153, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_153);
x_165 = lean_ctor_get(x_151, 0);
lean_inc_ref(x_165);
x_166 = lean_ctor_get_uint8(x_151, sizeof(void*)*3);
x_167 = lean_ctor_get(x_151, 2);
lean_inc(x_167);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 lean_ctor_release(x_151, 2);
 x_168 = x_151;
} else {
 lean_dec_ref(x_151);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(0, 3, 1);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_165);
lean_ctor_set(x_169, 1, x_163);
lean_ctor_set(x_169, 2, x_167);
lean_ctor_set_uint8(x_169, sizeof(void*)*3, x_166);
lean_ctor_set(x_147, 1, x_169);
lean_ctor_set(x_147, 0, x_1);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_147);
lean_ctor_set(x_170, 1, x_164);
return x_170;
}
}
else
{
lean_object* x_171; lean_object* x_172; uint64_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_171 = lean_ctor_get(x_147, 0);
x_172 = lean_ctor_get(x_147, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_147);
x_173 = lean_unbox_uint64(x_171);
lean_dec(x_171);
lean_inc_ref(x_1);
x_174 = l_Lake_computeArtifactTrace(x_1, x_1, x_173, x_148);
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
x_178 = lean_ctor_get(x_172, 0);
lean_inc_ref(x_178);
x_179 = lean_ctor_get_uint8(x_172, sizeof(void*)*3);
x_180 = lean_ctor_get(x_172, 2);
lean_inc(x_180);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 lean_ctor_release(x_172, 2);
 x_181 = x_172;
} else {
 lean_dec_ref(x_172);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(0, 3, 1);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_178);
lean_ctor_set(x_182, 1, x_175);
lean_ctor_set(x_182, 2, x_180);
lean_ctor_set_uint8(x_182, sizeof(void*)*3, x_179);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_1);
lean_ctor_set(x_183, 1, x_182);
if (lean_is_scalar(x_177)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_177;
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_176);
return x_184;
}
}
else
{
uint8_t x_185; 
lean_dec_ref(x_1);
x_185 = !lean_is_exclusive(x_146);
if (x_185 == 0)
{
lean_object* x_186; uint8_t x_187; 
x_186 = lean_ctor_get(x_146, 0);
lean_dec(x_186);
x_187 = !lean_is_exclusive(x_147);
if (x_187 == 0)
{
return x_146;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_147, 0);
x_189 = lean_ctor_get(x_147, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_147);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
lean_ctor_set(x_146, 0, x_190);
return x_146;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_191 = lean_ctor_get(x_146, 1);
lean_inc(x_191);
lean_dec(x_146);
x_192 = lean_ctor_get(x_147, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_147, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_194 = x_147;
} else {
 lean_dec_ref(x_147);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_193);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_191);
return x_196;
}
}
}
}
}
else
{
lean_object* x_494; uint8_t x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_588; 
x_494 = lean_ctor_get(x_12, 0);
x_495 = lean_ctor_get_uint8(x_12, sizeof(void*)*3);
x_496 = lean_ctor_get(x_12, 1);
x_497 = lean_ctor_get(x_12, 2);
lean_inc(x_497);
lean_inc(x_496);
lean_inc(x_494);
lean_dec(x_12);
x_498 = l_Lake_buildFileUnlessUpToDate_x27___closed__0;
lean_inc_ref(x_1);
x_499 = lean_string_append(x_1, x_498);
lean_inc_ref(x_499);
x_500 = l_Lake_readTraceFile(x_499, x_494, x_13);
x_501 = lean_ctor_get(x_500, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_500, 1);
lean_inc(x_502);
lean_dec_ref(x_500);
x_503 = lean_ctor_get(x_501, 0);
lean_inc(x_503);
x_504 = lean_ctor_get(x_501, 1);
lean_inc(x_504);
if (lean_is_exclusive(x_501)) {
 lean_ctor_release(x_501, 0);
 lean_ctor_release(x_501, 1);
 x_505 = x_501;
} else {
 lean_dec_ref(x_501);
 x_505 = lean_box(0);
}
lean_inc_ref(x_496);
x_588 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_588, 0, x_504);
lean_ctor_set(x_588, 1, x_496);
lean_ctor_set(x_588, 2, x_497);
lean_ctor_set_uint8(x_588, sizeof(void*)*3, x_495);
if (lean_obj_tag(x_8) == 0)
{
lean_dec(x_505);
x_506 = x_7;
x_507 = x_8;
x_508 = x_9;
x_509 = x_10;
x_510 = x_11;
x_511 = x_588;
x_512 = x_502;
goto block_587;
}
else
{
lean_object* x_589; lean_object* x_590; 
x_589 = lean_ctor_get(x_8, 0);
x_590 = lean_ctor_get(x_589, 19);
if (lean_obj_tag(x_590) == 0)
{
lean_dec(x_505);
x_506 = x_7;
x_507 = x_8;
x_508 = x_9;
x_509 = x_10;
x_510 = x_11;
x_511 = x_588;
x_512 = x_502;
goto block_587;
}
else
{
lean_object* x_591; uint64_t x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_632; lean_object* x_633; 
x_591 = lean_ctor_get(x_590, 0);
x_592 = lean_ctor_get_uint64(x_496, sizeof(void*)*3);
x_593 = lean_ctor_get(x_496, 2);
lean_inc_ref(x_11);
lean_inc(x_503);
x_632 = l_Lake_resolveArtifactsUsing_x3f___at___Lake_buildArtifactUnlessUpToDate_spec__0(x_4, x_7, x_592, x_499, x_503, x_591, x_8, x_9, x_10, x_11, x_588, x_502);
x_633 = lean_ctor_get(x_632, 0);
lean_inc(x_633);
if (lean_obj_tag(x_633) == 0)
{
lean_object* x_634; 
x_634 = lean_ctor_get(x_633, 0);
if (lean_obj_tag(x_634) == 0)
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; uint8_t x_640; 
lean_inc(x_591);
x_635 = lean_ctor_get(x_632, 1);
lean_inc(x_635);
lean_dec_ref(x_632);
x_636 = lean_ctor_get(x_633, 1);
lean_inc(x_636);
lean_dec_ref(x_633);
x_637 = l_Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0___redArg(x_1, x_496, x_503, x_593, x_11, x_636, x_635);
x_638 = lean_ctor_get(x_637, 0);
lean_inc(x_638);
x_639 = lean_ctor_get(x_638, 0);
x_640 = lean_unbox(x_639);
if (x_640 == 0)
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; 
x_641 = lean_ctor_get(x_637, 1);
lean_inc(x_641);
lean_dec_ref(x_637);
x_642 = lean_ctor_get(x_638, 1);
lean_inc(x_642);
lean_dec(x_638);
lean_inc_ref(x_11);
lean_inc_ref(x_1);
x_643 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_3, x_496, x_499, x_7, x_8, x_9, x_10, x_11, x_642, x_641);
lean_dec_ref(x_499);
lean_dec_ref(x_496);
x_644 = lean_ctor_get(x_643, 0);
lean_inc(x_644);
if (lean_obj_tag(x_644) == 0)
{
lean_object* x_645; lean_object* x_646; 
x_645 = lean_ctor_get(x_643, 1);
lean_inc(x_645);
lean_dec_ref(x_643);
x_646 = lean_ctor_get(x_644, 1);
lean_inc(x_646);
lean_dec_ref(x_644);
x_594 = x_11;
x_595 = x_646;
x_596 = x_645;
goto block_631;
}
else
{
lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; 
lean_dec(x_591);
lean_dec(x_505);
lean_dec_ref(x_11);
lean_dec_ref(x_1);
x_647 = lean_ctor_get(x_643, 1);
lean_inc(x_647);
if (lean_is_exclusive(x_643)) {
 lean_ctor_release(x_643, 0);
 lean_ctor_release(x_643, 1);
 x_648 = x_643;
} else {
 lean_dec_ref(x_643);
 x_648 = lean_box(0);
}
x_649 = lean_ctor_get(x_644, 0);
lean_inc(x_649);
x_650 = lean_ctor_get(x_644, 1);
lean_inc(x_650);
if (lean_is_exclusive(x_644)) {
 lean_ctor_release(x_644, 0);
 lean_ctor_release(x_644, 1);
 x_651 = x_644;
} else {
 lean_dec_ref(x_644);
 x_651 = lean_box(0);
}
if (lean_is_scalar(x_651)) {
 x_652 = lean_alloc_ctor(1, 2, 0);
} else {
 x_652 = x_651;
}
lean_ctor_set(x_652, 0, x_649);
lean_ctor_set(x_652, 1, x_650);
if (lean_is_scalar(x_648)) {
 x_653 = lean_alloc_ctor(0, 2, 0);
} else {
 x_653 = x_648;
}
lean_ctor_set(x_653, 0, x_652);
lean_ctor_set(x_653, 1, x_647);
return x_653;
}
}
else
{
lean_object* x_654; lean_object* x_655; 
lean_dec_ref(x_499);
lean_dec_ref(x_496);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_654 = lean_ctor_get(x_637, 1);
lean_inc(x_654);
lean_dec_ref(x_637);
x_655 = lean_ctor_get(x_638, 1);
lean_inc(x_655);
lean_dec(x_638);
x_594 = x_11;
x_595 = x_655;
x_596 = x_654;
goto block_631;
}
}
else
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; uint8_t x_665; lean_object* x_666; lean_object* x_667; 
lean_inc_ref(x_634);
lean_dec(x_505);
lean_dec(x_503);
lean_dec_ref(x_499);
lean_dec_ref(x_496);
lean_dec_ref(x_2);
x_656 = lean_ctor_get(x_632, 1);
lean_inc(x_656);
lean_dec_ref(x_632);
x_657 = lean_ctor_get(x_633, 1);
lean_inc(x_657);
if (lean_is_exclusive(x_633)) {
 lean_ctor_release(x_633, 0);
 lean_ctor_release(x_633, 1);
 x_658 = x_633;
} else {
 lean_dec_ref(x_633);
 x_658 = lean_box(0);
}
x_659 = lean_ctor_get(x_634, 0);
lean_inc(x_659);
lean_dec_ref(x_634);
x_660 = l_System_FilePath_pathExists(x_1, x_656);
x_661 = lean_ctor_get(x_660, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_660, 1);
lean_inc(x_662);
if (lean_is_exclusive(x_660)) {
 lean_ctor_release(x_660, 0);
 lean_ctor_release(x_660, 1);
 x_663 = x_660;
} else {
 lean_dec_ref(x_660);
 x_663 = lean_box(0);
}
x_664 = lean_ctor_get(x_657, 0);
x_665 = lean_ctor_get_uint8(x_657, sizeof(void*)*3);
x_666 = lean_ctor_get(x_657, 1);
x_667 = lean_ctor_get(x_657, 2);
if (x_5 == 0)
{
lean_dec(x_663);
lean_dec(x_661);
lean_dec(x_658);
goto block_670;
}
else
{
uint8_t x_671; 
x_671 = lean_unbox(x_661);
lean_dec(x_661);
if (x_671 == 0)
{
lean_object* x_672; lean_object* x_673; uint64_t x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; uint8_t x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_702; lean_object* x_703; uint8_t x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; 
lean_inc(x_667);
lean_inc_ref(x_666);
lean_inc_ref(x_664);
if (lean_is_exclusive(x_657)) {
 lean_ctor_release(x_657, 0);
 lean_ctor_release(x_657, 1);
 lean_ctor_release(x_657, 2);
 x_672 = x_657;
} else {
 lean_dec_ref(x_657);
 x_672 = lean_box(0);
}
x_673 = lean_ctor_get(x_659, 0);
x_674 = lean_ctor_get_uint64(x_659, sizeof(void*)*3);
x_702 = l_Lake_buildArtifactUnlessUpToDate___closed__0;
x_703 = lean_string_append(x_702, x_1);
x_704 = 0;
x_705 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_705, 0, x_703);
lean_ctor_set_uint8(x_705, sizeof(void*)*1, x_704);
x_706 = lean_array_push(x_664, x_705);
x_707 = l_Lake_copyFile(x_673, x_1, x_662);
if (lean_obj_tag(x_707) == 0)
{
if (x_6 == 0)
{
lean_object* x_708; lean_object* x_709; 
lean_dec(x_663);
x_708 = lean_ctor_get(x_707, 1);
lean_inc(x_708);
lean_dec_ref(x_707);
lean_inc(x_667);
lean_inc_ref(x_666);
lean_inc_ref(x_706);
x_709 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_709, 0, x_706);
lean_ctor_set(x_709, 1, x_666);
lean_ctor_set(x_709, 2, x_667);
lean_ctor_set_uint8(x_709, sizeof(void*)*3, x_665);
x_675 = x_7;
x_676 = x_8;
x_677 = x_9;
x_678 = x_10;
x_679 = x_11;
x_680 = x_709;
x_681 = x_706;
x_682 = x_665;
x_683 = x_666;
x_684 = x_667;
x_685 = x_708;
goto block_701;
}
else
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; 
x_710 = lean_ctor_get(x_707, 1);
lean_inc(x_710);
lean_dec_ref(x_707);
x_711 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_711, 0, x_5);
lean_ctor_set_uint8(x_711, 1, x_5);
lean_ctor_set_uint8(x_711, 2, x_5);
lean_inc_ref_n(x_711, 2);
x_712 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_712, 0, x_711);
lean_ctor_set(x_712, 1, x_711);
lean_ctor_set(x_712, 2, x_711);
x_713 = l_IO_setAccessRights(x_1, x_712, x_710);
lean_dec_ref(x_712);
if (lean_obj_tag(x_713) == 0)
{
lean_object* x_714; lean_object* x_715; 
lean_dec(x_663);
x_714 = lean_ctor_get(x_713, 1);
lean_inc(x_714);
lean_dec_ref(x_713);
lean_inc(x_667);
lean_inc_ref(x_666);
lean_inc_ref(x_706);
x_715 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_715, 0, x_706);
lean_ctor_set(x_715, 1, x_666);
lean_ctor_set(x_715, 2, x_667);
lean_ctor_set_uint8(x_715, sizeof(void*)*3, x_665);
x_675 = x_7;
x_676 = x_8;
x_677 = x_9;
x_678 = x_10;
x_679 = x_11;
x_680 = x_715;
x_681 = x_706;
x_682 = x_665;
x_683 = x_666;
x_684 = x_667;
x_685 = x_714;
goto block_701;
}
else
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; uint8_t x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; 
lean_dec(x_672);
lean_dec(x_659);
lean_dec(x_658);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_716 = lean_ctor_get(x_713, 0);
lean_inc(x_716);
x_717 = lean_ctor_get(x_713, 1);
lean_inc(x_717);
if (lean_is_exclusive(x_713)) {
 lean_ctor_release(x_713, 0);
 lean_ctor_release(x_713, 1);
 x_718 = x_713;
} else {
 lean_dec_ref(x_713);
 x_718 = lean_box(0);
}
x_719 = lean_io_error_to_string(x_716);
x_720 = 3;
x_721 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_721, 0, x_719);
lean_ctor_set_uint8(x_721, sizeof(void*)*1, x_720);
x_722 = lean_array_get_size(x_706);
x_723 = lean_array_push(x_706, x_721);
x_724 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_724, 0, x_723);
lean_ctor_set(x_724, 1, x_666);
lean_ctor_set(x_724, 2, x_667);
lean_ctor_set_uint8(x_724, sizeof(void*)*3, x_665);
if (lean_is_scalar(x_663)) {
 x_725 = lean_alloc_ctor(1, 2, 0);
} else {
 x_725 = x_663;
 lean_ctor_set_tag(x_725, 1);
}
lean_ctor_set(x_725, 0, x_722);
lean_ctor_set(x_725, 1, x_724);
if (lean_is_scalar(x_718)) {
 x_726 = lean_alloc_ctor(0, 2, 0);
} else {
 x_726 = x_718;
 lean_ctor_set_tag(x_726, 0);
}
lean_ctor_set(x_726, 0, x_725);
lean_ctor_set(x_726, 1, x_717);
return x_726;
}
}
}
else
{
lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; uint8_t x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; 
lean_dec(x_672);
lean_dec(x_659);
lean_dec(x_658);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_727 = lean_ctor_get(x_707, 0);
lean_inc(x_727);
x_728 = lean_ctor_get(x_707, 1);
lean_inc(x_728);
if (lean_is_exclusive(x_707)) {
 lean_ctor_release(x_707, 0);
 lean_ctor_release(x_707, 1);
 x_729 = x_707;
} else {
 lean_dec_ref(x_707);
 x_729 = lean_box(0);
}
x_730 = lean_io_error_to_string(x_727);
x_731 = 3;
x_732 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_732, 0, x_730);
lean_ctor_set_uint8(x_732, sizeof(void*)*1, x_731);
x_733 = lean_array_get_size(x_706);
x_734 = lean_array_push(x_706, x_732);
x_735 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_735, 0, x_734);
lean_ctor_set(x_735, 1, x_666);
lean_ctor_set(x_735, 2, x_667);
lean_ctor_set_uint8(x_735, sizeof(void*)*3, x_665);
if (lean_is_scalar(x_663)) {
 x_736 = lean_alloc_ctor(1, 2, 0);
} else {
 x_736 = x_663;
 lean_ctor_set_tag(x_736, 1);
}
lean_ctor_set(x_736, 0, x_733);
lean_ctor_set(x_736, 1, x_735);
if (lean_is_scalar(x_729)) {
 x_737 = lean_alloc_ctor(0, 2, 0);
} else {
 x_737 = x_729;
 lean_ctor_set_tag(x_737, 0);
}
lean_ctor_set(x_737, 0, x_736);
lean_ctor_set(x_737, 1, x_728);
return x_737;
}
block_701:
{
lean_object* x_686; 
lean_inc_ref(x_1);
x_686 = l_Lake_writeFileHash(x_1, x_674, x_685);
if (lean_obj_tag(x_686) == 0)
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; 
lean_dec(x_684);
lean_dec_ref(x_683);
lean_dec_ref(x_681);
lean_dec(x_672);
lean_dec(x_658);
x_687 = lean_ctor_get(x_686, 0);
lean_inc(x_687);
x_688 = lean_ctor_get(x_686, 1);
lean_inc(x_688);
lean_dec_ref(x_686);
x_689 = l_Lake_buildArtifactUnlessUpToDate___lam__0(x_659, x_5, x_1, x_687, x_675, x_676, x_677, x_678, x_679, x_680, x_688);
lean_dec_ref(x_679);
lean_dec(x_678);
lean_dec(x_677);
lean_dec(x_676);
lean_dec_ref(x_675);
return x_689;
}
else
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; uint8_t x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; 
lean_dec_ref(x_680);
lean_dec_ref(x_679);
lean_dec(x_678);
lean_dec(x_677);
lean_dec(x_676);
lean_dec_ref(x_675);
lean_dec(x_659);
lean_dec_ref(x_1);
x_690 = lean_ctor_get(x_686, 0);
lean_inc(x_690);
x_691 = lean_ctor_get(x_686, 1);
lean_inc(x_691);
if (lean_is_exclusive(x_686)) {
 lean_ctor_release(x_686, 0);
 lean_ctor_release(x_686, 1);
 x_692 = x_686;
} else {
 lean_dec_ref(x_686);
 x_692 = lean_box(0);
}
x_693 = lean_io_error_to_string(x_690);
x_694 = 3;
x_695 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_695, 0, x_693);
lean_ctor_set_uint8(x_695, sizeof(void*)*1, x_694);
x_696 = lean_array_get_size(x_681);
x_697 = lean_array_push(x_681, x_695);
if (lean_is_scalar(x_672)) {
 x_698 = lean_alloc_ctor(0, 3, 1);
} else {
 x_698 = x_672;
}
lean_ctor_set(x_698, 0, x_697);
lean_ctor_set(x_698, 1, x_683);
lean_ctor_set(x_698, 2, x_684);
lean_ctor_set_uint8(x_698, sizeof(void*)*3, x_682);
if (lean_is_scalar(x_658)) {
 x_699 = lean_alloc_ctor(1, 2, 0);
} else {
 x_699 = x_658;
 lean_ctor_set_tag(x_699, 1);
}
lean_ctor_set(x_699, 0, x_696);
lean_ctor_set(x_699, 1, x_698);
if (lean_is_scalar(x_692)) {
 x_700 = lean_alloc_ctor(0, 2, 0);
} else {
 x_700 = x_692;
 lean_ctor_set_tag(x_700, 0);
}
lean_ctor_set(x_700, 0, x_699);
lean_ctor_set(x_700, 1, x_691);
return x_700;
}
}
}
else
{
lean_dec(x_663);
lean_dec(x_658);
goto block_670;
}
}
block_670:
{
lean_object* x_668; lean_object* x_669; 
x_668 = lean_box(0);
x_669 = l_Lake_buildArtifactUnlessUpToDate___lam__0(x_659, x_5, x_1, x_668, x_7, x_8, x_9, x_10, x_11, x_657, x_662);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
return x_669;
}
}
}
else
{
lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; 
lean_dec(x_505);
lean_dec(x_503);
lean_dec_ref(x_499);
lean_dec_ref(x_496);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_738 = lean_ctor_get(x_632, 1);
lean_inc(x_738);
if (lean_is_exclusive(x_632)) {
 lean_ctor_release(x_632, 0);
 lean_ctor_release(x_632, 1);
 x_739 = x_632;
} else {
 lean_dec_ref(x_632);
 x_739 = lean_box(0);
}
x_740 = lean_ctor_get(x_633, 0);
lean_inc(x_740);
x_741 = lean_ctor_get(x_633, 1);
lean_inc(x_741);
if (lean_is_exclusive(x_633)) {
 lean_ctor_release(x_633, 0);
 lean_ctor_release(x_633, 1);
 x_742 = x_633;
} else {
 lean_dec_ref(x_633);
 x_742 = lean_box(0);
}
if (lean_is_scalar(x_742)) {
 x_743 = lean_alloc_ctor(1, 2, 0);
} else {
 x_743 = x_742;
}
lean_ctor_set(x_743, 0, x_740);
lean_ctor_set(x_743, 1, x_741);
if (lean_is_scalar(x_739)) {
 x_744 = lean_alloc_ctor(0, 2, 0);
} else {
 x_744 = x_739;
}
lean_ctor_set(x_744, 0, x_743);
lean_ctor_set(x_744, 1, x_738);
return x_744;
}
block_631:
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; uint8_t x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; 
x_597 = lean_ctor_get(x_594, 1);
lean_inc(x_597);
lean_dec_ref(x_594);
x_598 = lean_ctor_get(x_597, 1);
lean_inc_ref(x_598);
lean_dec(x_597);
x_599 = lean_ctor_get(x_595, 0);
lean_inc_ref(x_599);
x_600 = lean_ctor_get_uint8(x_595, sizeof(void*)*3);
x_601 = lean_ctor_get(x_595, 1);
lean_inc_ref(x_601);
x_602 = lean_ctor_get(x_595, 2);
lean_inc(x_602);
if (lean_is_exclusive(x_595)) {
 lean_ctor_release(x_595, 0);
 lean_ctor_release(x_595, 1);
 lean_ctor_release(x_595, 2);
 x_603 = x_595;
} else {
 lean_dec_ref(x_595);
 x_603 = lean_box(0);
}
x_604 = lean_ctor_get(x_598, 6);
lean_inc_ref(x_604);
lean_dec_ref(x_598);
lean_inc_ref(x_1);
x_605 = l_Lake_Cache_saveArtifact(x_604, x_1, x_4, x_3, x_6, x_596);
if (lean_obj_tag(x_605) == 0)
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; uint64_t x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; 
lean_dec_ref(x_601);
lean_dec(x_505);
x_606 = lean_ctor_get(x_605, 0);
lean_inc(x_606);
x_607 = lean_ctor_get(x_605, 1);
lean_inc(x_607);
lean_dec_ref(x_605);
x_608 = lean_st_ref_take(x_591, x_607);
x_609 = lean_ctor_get(x_608, 0);
lean_inc(x_609);
x_610 = lean_ctor_get(x_608, 1);
lean_inc(x_610);
lean_dec_ref(x_608);
x_611 = lean_ctor_get(x_606, 0);
lean_inc_ref(x_611);
x_612 = lean_ctor_get_uint64(x_606, sizeof(void*)*3);
x_613 = lean_uint64_to_nat(x_612);
x_614 = l_Lean_bignumToJson(x_613);
x_615 = l_Lake_CacheMap_insertCore(x_592, x_614, x_609);
x_616 = lean_st_ref_set(x_591, x_615, x_610);
lean_dec(x_591);
x_617 = lean_ctor_get(x_616, 1);
lean_inc(x_617);
lean_dec_ref(x_616);
x_618 = l_Lake_Artifact_trace(x_606);
if (lean_is_scalar(x_603)) {
 x_619 = lean_alloc_ctor(0, 3, 1);
} else {
 x_619 = x_603;
}
lean_ctor_set(x_619, 0, x_599);
lean_ctor_set(x_619, 1, x_618);
lean_ctor_set(x_619, 2, x_602);
lean_ctor_set_uint8(x_619, sizeof(void*)*3, x_600);
if (x_5 == 0)
{
lean_dec_ref(x_1);
x_14 = x_619;
x_15 = x_617;
x_16 = x_611;
goto block_19;
}
else
{
lean_dec_ref(x_611);
x_14 = x_619;
x_15 = x_617;
x_16 = x_1;
goto block_19;
}
}
else
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; uint8_t x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; 
lean_dec(x_591);
lean_dec_ref(x_1);
x_620 = lean_ctor_get(x_605, 0);
lean_inc(x_620);
x_621 = lean_ctor_get(x_605, 1);
lean_inc(x_621);
if (lean_is_exclusive(x_605)) {
 lean_ctor_release(x_605, 0);
 lean_ctor_release(x_605, 1);
 x_622 = x_605;
} else {
 lean_dec_ref(x_605);
 x_622 = lean_box(0);
}
x_623 = lean_io_error_to_string(x_620);
x_624 = 3;
x_625 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_625, 0, x_623);
lean_ctor_set_uint8(x_625, sizeof(void*)*1, x_624);
x_626 = lean_array_get_size(x_599);
x_627 = lean_array_push(x_599, x_625);
if (lean_is_scalar(x_603)) {
 x_628 = lean_alloc_ctor(0, 3, 1);
} else {
 x_628 = x_603;
}
lean_ctor_set(x_628, 0, x_627);
lean_ctor_set(x_628, 1, x_601);
lean_ctor_set(x_628, 2, x_602);
lean_ctor_set_uint8(x_628, sizeof(void*)*3, x_600);
if (lean_is_scalar(x_505)) {
 x_629 = lean_alloc_ctor(1, 2, 0);
} else {
 x_629 = x_505;
 lean_ctor_set_tag(x_629, 1);
}
lean_ctor_set(x_629, 0, x_626);
lean_ctor_set(x_629, 1, x_628);
if (lean_is_scalar(x_622)) {
 x_630 = lean_alloc_ctor(0, 2, 0);
} else {
 x_630 = x_622;
 lean_ctor_set_tag(x_630, 0);
}
lean_ctor_set(x_630, 0, x_629);
lean_ctor_set(x_630, 1, x_621);
return x_630;
}
}
}
}
block_587:
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; uint8_t x_517; 
x_513 = lean_ctor_get(x_496, 2);
x_514 = l_Lake_SavedTrace_replayIfUpToDate___at___Lake_buildFileUnlessUpToDate_x27_spec__0___redArg(x_1, x_496, x_503, x_513, x_510, x_511, x_512);
x_515 = lean_ctor_get(x_514, 0);
lean_inc(x_515);
x_516 = lean_ctor_get(x_515, 0);
x_517 = lean_unbox(x_516);
if (x_517 == 0)
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
x_518 = lean_ctor_get(x_514, 1);
lean_inc(x_518);
lean_dec_ref(x_514);
x_519 = lean_ctor_get(x_515, 1);
lean_inc(x_519);
lean_dec(x_515);
lean_inc_ref(x_1);
x_520 = l___private_Lake_Build_Common_0__Lake_buildArtifactUnlessUpToDate_doBuild(x_1, x_2, x_3, x_496, x_499, x_506, x_507, x_508, x_509, x_510, x_519, x_518);
lean_dec_ref(x_499);
lean_dec_ref(x_496);
x_521 = lean_ctor_get(x_520, 0);
lean_inc(x_521);
if (lean_obj_tag(x_521) == 0)
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; uint8_t x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; uint64_t x_531; lean_object* x_532; 
x_522 = lean_ctor_get(x_521, 1);
lean_inc(x_522);
x_523 = lean_ctor_get(x_520, 1);
lean_inc(x_523);
lean_dec_ref(x_520);
x_524 = lean_ctor_get(x_521, 0);
lean_inc(x_524);
if (lean_is_exclusive(x_521)) {
 lean_ctor_release(x_521, 0);
 lean_ctor_release(x_521, 1);
 x_525 = x_521;
} else {
 lean_dec_ref(x_521);
 x_525 = lean_box(0);
}
x_526 = lean_ctor_get(x_522, 0);
lean_inc_ref(x_526);
x_527 = lean_ctor_get_uint8(x_522, sizeof(void*)*3);
x_528 = lean_ctor_get(x_522, 1);
lean_inc_ref(x_528);
x_529 = lean_ctor_get(x_522, 2);
lean_inc(x_529);
if (lean_is_exclusive(x_522)) {
 lean_ctor_release(x_522, 0);
 lean_ctor_release(x_522, 1);
 lean_ctor_release(x_522, 2);
 x_530 = x_522;
} else {
 lean_dec_ref(x_522);
 x_530 = lean_box(0);
}
x_531 = lean_unbox_uint64(x_524);
lean_inc_ref(x_1);
x_532 = l_Lake_writeFileHash(x_1, x_531, x_523);
if (lean_obj_tag(x_532) == 0)
{
lean_object* x_533; uint64_t x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; 
lean_dec_ref(x_528);
x_533 = lean_ctor_get(x_532, 1);
lean_inc(x_533);
lean_dec_ref(x_532);
x_534 = lean_unbox_uint64(x_524);
lean_dec(x_524);
lean_inc_ref(x_1);
x_535 = l_Lake_computeArtifactTrace(x_1, x_1, x_534, x_533);
x_536 = lean_ctor_get(x_535, 0);
lean_inc(x_536);
x_537 = lean_ctor_get(x_535, 1);
lean_inc(x_537);
if (lean_is_exclusive(x_535)) {
 lean_ctor_release(x_535, 0);
 lean_ctor_release(x_535, 1);
 x_538 = x_535;
} else {
 lean_dec_ref(x_535);
 x_538 = lean_box(0);
}
if (lean_is_scalar(x_530)) {
 x_539 = lean_alloc_ctor(0, 3, 1);
} else {
 x_539 = x_530;
}
lean_ctor_set(x_539, 0, x_526);
lean_ctor_set(x_539, 1, x_536);
lean_ctor_set(x_539, 2, x_529);
lean_ctor_set_uint8(x_539, sizeof(void*)*3, x_527);
if (lean_is_scalar(x_525)) {
 x_540 = lean_alloc_ctor(0, 2, 0);
} else {
 x_540 = x_525;
}
lean_ctor_set(x_540, 0, x_1);
lean_ctor_set(x_540, 1, x_539);
if (lean_is_scalar(x_538)) {
 x_541 = lean_alloc_ctor(0, 2, 0);
} else {
 x_541 = x_538;
}
lean_ctor_set(x_541, 0, x_540);
lean_ctor_set(x_541, 1, x_537);
return x_541;
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; uint8_t x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; 
lean_dec(x_524);
lean_dec_ref(x_1);
x_542 = lean_ctor_get(x_532, 0);
lean_inc(x_542);
x_543 = lean_ctor_get(x_532, 1);
lean_inc(x_543);
if (lean_is_exclusive(x_532)) {
 lean_ctor_release(x_532, 0);
 lean_ctor_release(x_532, 1);
 x_544 = x_532;
} else {
 lean_dec_ref(x_532);
 x_544 = lean_box(0);
}
x_545 = lean_io_error_to_string(x_542);
x_546 = 3;
x_547 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_547, 0, x_545);
lean_ctor_set_uint8(x_547, sizeof(void*)*1, x_546);
x_548 = lean_array_get_size(x_526);
x_549 = lean_array_push(x_526, x_547);
if (lean_is_scalar(x_530)) {
 x_550 = lean_alloc_ctor(0, 3, 1);
} else {
 x_550 = x_530;
}
lean_ctor_set(x_550, 0, x_549);
lean_ctor_set(x_550, 1, x_528);
lean_ctor_set(x_550, 2, x_529);
lean_ctor_set_uint8(x_550, sizeof(void*)*3, x_527);
if (lean_is_scalar(x_525)) {
 x_551 = lean_alloc_ctor(1, 2, 0);
} else {
 x_551 = x_525;
 lean_ctor_set_tag(x_551, 1);
}
lean_ctor_set(x_551, 0, x_548);
lean_ctor_set(x_551, 1, x_550);
if (lean_is_scalar(x_544)) {
 x_552 = lean_alloc_ctor(0, 2, 0);
} else {
 x_552 = x_544;
 lean_ctor_set_tag(x_552, 0);
}
lean_ctor_set(x_552, 0, x_551);
lean_ctor_set(x_552, 1, x_543);
return x_552;
}
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; 
lean_dec_ref(x_1);
x_553 = lean_ctor_get(x_520, 1);
lean_inc(x_553);
if (lean_is_exclusive(x_520)) {
 lean_ctor_release(x_520, 0);
 lean_ctor_release(x_520, 1);
 x_554 = x_520;
} else {
 lean_dec_ref(x_520);
 x_554 = lean_box(0);
}
x_555 = lean_ctor_get(x_521, 0);
lean_inc(x_555);
x_556 = lean_ctor_get(x_521, 1);
lean_inc(x_556);
if (lean_is_exclusive(x_521)) {
 lean_ctor_release(x_521, 0);
 lean_ctor_release(x_521, 1);
 x_557 = x_521;
} else {
 lean_dec_ref(x_521);
 x_557 = lean_box(0);
}
if (lean_is_scalar(x_557)) {
 x_558 = lean_alloc_ctor(1, 2, 0);
} else {
 x_558 = x_557;
}
lean_ctor_set(x_558, 0, x_555);
lean_ctor_set(x_558, 1, x_556);
if (lean_is_scalar(x_554)) {
 x_559 = lean_alloc_ctor(0, 2, 0);
} else {
 x_559 = x_554;
}
lean_ctor_set(x_559, 0, x_558);
lean_ctor_set(x_559, 1, x_553);
return x_559;
}
}
else
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; 
lean_dec(x_509);
lean_dec(x_508);
lean_dec(x_507);
lean_dec_ref(x_506);
lean_dec_ref(x_499);
lean_dec_ref(x_496);
lean_dec_ref(x_2);
x_560 = lean_ctor_get(x_514, 1);
lean_inc(x_560);
lean_dec_ref(x_514);
x_561 = lean_ctor_get(x_515, 1);
lean_inc(x_561);
lean_dec(x_515);
lean_inc_ref(x_1);
x_562 = l_Lake_fetchFileHash___redArg(x_1, x_3, x_510, x_561, x_560);
lean_dec_ref(x_510);
x_563 = lean_ctor_get(x_562, 0);
lean_inc(x_563);
if (lean_obj_tag(x_563) == 0)
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; uint64_t x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; uint8_t x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; 
x_564 = lean_ctor_get(x_562, 1);
lean_inc(x_564);
lean_dec_ref(x_562);
x_565 = lean_ctor_get(x_563, 0);
lean_inc(x_565);
x_566 = lean_ctor_get(x_563, 1);
lean_inc(x_566);
if (lean_is_exclusive(x_563)) {
 lean_ctor_release(x_563, 0);
 lean_ctor_release(x_563, 1);
 x_567 = x_563;
} else {
 lean_dec_ref(x_563);
 x_567 = lean_box(0);
}
x_568 = lean_unbox_uint64(x_565);
lean_dec(x_565);
lean_inc_ref(x_1);
x_569 = l_Lake_computeArtifactTrace(x_1, x_1, x_568, x_564);
x_570 = lean_ctor_get(x_569, 0);
lean_inc(x_570);
x_571 = lean_ctor_get(x_569, 1);
lean_inc(x_571);
if (lean_is_exclusive(x_569)) {
 lean_ctor_release(x_569, 0);
 lean_ctor_release(x_569, 1);
 x_572 = x_569;
} else {
 lean_dec_ref(x_569);
 x_572 = lean_box(0);
}
x_573 = lean_ctor_get(x_566, 0);
lean_inc_ref(x_573);
x_574 = lean_ctor_get_uint8(x_566, sizeof(void*)*3);
x_575 = lean_ctor_get(x_566, 2);
lean_inc(x_575);
if (lean_is_exclusive(x_566)) {
 lean_ctor_release(x_566, 0);
 lean_ctor_release(x_566, 1);
 lean_ctor_release(x_566, 2);
 x_576 = x_566;
} else {
 lean_dec_ref(x_566);
 x_576 = lean_box(0);
}
if (lean_is_scalar(x_576)) {
 x_577 = lean_alloc_ctor(0, 3, 1);
} else {
 x_577 = x_576;
}
lean_ctor_set(x_577, 0, x_573);
lean_ctor_set(x_577, 1, x_570);
lean_ctor_set(x_577, 2, x_575);
lean_ctor_set_uint8(x_577, sizeof(void*)*3, x_574);
if (lean_is_scalar(x_567)) {
 x_578 = lean_alloc_ctor(0, 2, 0);
} else {
 x_578 = x_567;
}
lean_ctor_set(x_578, 0, x_1);
lean_ctor_set(x_578, 1, x_577);
if (lean_is_scalar(x_572)) {
 x_579 = lean_alloc_ctor(0, 2, 0);
} else {
 x_579 = x_572;
}
lean_ctor_set(x_579, 0, x_578);
lean_ctor_set(x_579, 1, x_571);
return x_579;
}
else
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; 
lean_dec_ref(x_1);
x_580 = lean_ctor_get(x_562, 1);
lean_inc(x_580);
if (lean_is_exclusive(x_562)) {
 lean_ctor_release(x_562, 0);
 lean_ctor_release(x_562, 1);
 x_581 = x_562;
} else {
 lean_dec_ref(x_562);
 x_581 = lean_box(0);
}
x_582 = lean_ctor_get(x_563, 0);
lean_inc(x_582);
x_583 = lean_ctor_get(x_563, 1);
lean_inc(x_583);
if (lean_is_exclusive(x_563)) {
 lean_ctor_release(x_563, 0);
 lean_ctor_release(x_563, 1);
 x_584 = x_563;
} else {
 lean_dec_ref(x_563);
 x_584 = lean_box(0);
}
if (lean_is_scalar(x_584)) {
 x_585 = lean_alloc_ctor(1, 2, 0);
} else {
 x_585 = x_584;
}
lean_ctor_set(x_585, 0, x_582);
lean_ctor_set(x_585, 1, x_583);
if (lean_is_scalar(x_581)) {
 x_586 = lean_alloc_ctor(0, 2, 0);
} else {
 x_586 = x_581;
}
lean_ctor_set(x_586, 0, x_585);
lean_ctor_set(x_586, 1, x_580);
return x_586;
}
}
}
}
block_19:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lake_resolveArtifactsUsing_x3f___at___Lake_buildArtifactUnlessUpToDate_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint64_t x_13; lean_object* x_14; 
x_13 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_14 = l_Lake_resolveArtifactsUsing_x3f___at___Lake_buildArtifactUnlessUpToDate_spec__0(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
x_13 = l_Lake_buildArtifactUnlessUpToDate___lam__0(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_buildArtifactUnlessUpToDate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_unbox(x_3);
x_15 = lean_unbox(x_5);
x_16 = lean_unbox(x_6);
x_17 = l_Lake_buildArtifactUnlessUpToDate(x_1, x_2, x_14, x_4, x_15, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_4);
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
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
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
lean_dec_ref(x_13);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec_ref(x_14);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_15, 1);
x_20 = l_Lake_BuildTrace_mix(x_19, x_17);
lean_ctor_set(x_15, 1, x_20);
x_21 = lean_apply_1(x_2, x_5);
x_22 = l_Lake_buildFileAfterDep___redArg___lam__0___closed__0;
x_23 = 0;
x_24 = l_Lake_buildArtifactUnlessUpToDate(x_3, x_21, x_4, x_22, x_23, x_23, x_6, x_7, x_8, x_9, x_10, x_15, x_16);
return x_24;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get_uint8(x_15, sizeof(void*)*3);
x_27 = lean_ctor_get(x_15, 1);
x_28 = lean_ctor_get(x_15, 2);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_25);
lean_dec(x_15);
x_29 = l_Lake_BuildTrace_mix(x_27, x_17);
x_30 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*3, x_26);
x_31 = lean_apply_1(x_2, x_5);
x_32 = l_Lake_buildFileAfterDep___redArg___lam__0___closed__0;
x_33 = 0;
x_34 = l_Lake_buildArtifactUnlessUpToDate(x_3, x_31, x_4, x_32, x_33, x_33, x_6, x_7, x_8, x_9, x_10, x_30, x_16);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_35 = !lean_is_exclusive(x_13);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_13, 0);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_14);
if (x_37 == 0)
{
return x_13;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_14, 0);
x_39 = lean_ctor_get(x_14, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_14);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_13, 0, x_40);
return x_13;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_13, 1);
lean_inc(x_41);
lean_dec(x_13);
x_42 = lean_ctor_get(x_14, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_14, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_44 = x_14;
} else {
 lean_dec_ref(x_14);
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
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_18 = l_Lake_Job_mapM___redArg(x_15, x_2, x_14, x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
x_19 = l_Lake_Job_mapM___redArg(x_16, x_3, x_15, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
x_14 = l_Lake_buildFileAfterDep___redArg___lam__0(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
x_14 = l_Lake_buildFileAfterDep___redArg(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_6);
x_15 = l_Lake_buildFileAfterDep(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
lean_dec_ref(x_3);
x_6 = lean_io_metadata(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint64_t x_12; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_9);
lean_dec(x_8);
x_10 = l_Lake_platformTrace___closed__4;
x_11 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_11, 2, x_9);
x_12 = lean_unbox_uint64(x_4);
lean_dec(x_4);
lean_ctor_set_uint64(x_11, sizeof(void*)*3, x_12);
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_6);
x_15 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_15);
lean_dec(x_13);
x_16 = l_Lake_platformTrace___closed__4;
x_17 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_15);
x_18 = lean_unbox_uint64(x_4);
lean_dec(x_4);
lean_ctor_set_uint64(x_17, sizeof(void*)*3, x_18);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_14);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_4);
lean_dec_ref(x_1);
x_20 = !lean_is_exclusive(x_6);
if (x_20 == 0)
{
return x_6;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get(x_6, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_6);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec_ref(x_1);
x_24 = !lean_is_exclusive(x_3);
if (x_24 == 0)
{
return x_3;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_ctor_get(x_3, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_3);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
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
x_26 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1___redArg___lam__0(x_17, x_22, x_25, x_24, x_21);
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
x_42 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__1___redArg___lam__0(x_17, x_22, x_41, x_40, x_21);
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
x_26 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2___redArg___lam__0(x_17, x_22, x_25, x_24, x_21);
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
x_42 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2___redArg___lam__0(x_17, x_22, x_41, x_40, x_21);
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
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__4___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_26 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__4___redArg___lam__0(x_17, x_22, x_25, x_24, x_21);
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
x_42 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__4___redArg___lam__0(x_17, x_22, x_41, x_40, x_21);
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
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__4___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_3 = lean_unsigned_to_nat(133u);
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
x_55 = lean_alloc_closure((void*)(l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__4), 10, 3);
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
lean_ctor_set(x_14, 1, x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
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
x_39 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___closed__4;
x_40 = l_panic___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__3(x_39);
x_10 = x_33;
x_11 = x_32;
x_12 = x_36;
x_13 = x_40;
goto block_17;
}
else
{
lean_object* x_41; 
x_41 = lean_string_from_utf8_unchecked(x_37);
lean_dec_ref(x_37);
x_10 = x_33;
x_11 = x_32;
x_12 = x_36;
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
lean_inc_ref(x_1);
x_12 = l_Lake_BuildTrace_compute___at___Lake_inputBinFile_spec__0(x_1, x_8);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec_ref(x_11);
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
lean_dec_ref(x_1);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_io_error_to_string(x_21);
x_23 = 3;
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_23);
x_25 = lean_array_get_size(x_10);
x_26 = lean_array_push(x_10, x_24);
lean_ctor_set(x_7, 0, x_26);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_7);
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_27);
return x_12;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_12, 0);
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_12);
x_30 = lean_io_error_to_string(x_28);
x_31 = 3;
x_32 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_31);
x_33 = lean_array_get_size(x_10);
x_34 = lean_array_push(x_10, x_32);
lean_ctor_set(x_7, 0, x_34);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_7);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_29);
return x_36;
}
}
}
else
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_7, 0);
x_38 = lean_ctor_get_uint8(x_7, sizeof(void*)*3);
x_39 = lean_ctor_get(x_7, 1);
x_40 = lean_ctor_get(x_7, 2);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_37);
lean_dec(x_7);
lean_inc_ref(x_1);
x_41 = l_Lake_BuildTrace_compute___at___Lake_inputBinFile_spec__0(x_1, x_8);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec_ref(x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_45, 0, x_37);
lean_ctor_set(x_45, 1, x_42);
lean_ctor_set(x_45, 2, x_40);
lean_ctor_set_uint8(x_45, sizeof(void*)*3, x_38);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_45);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_43);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec_ref(x_1);
x_48 = lean_ctor_get(x_41, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_41, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_50 = x_41;
} else {
 lean_dec_ref(x_41);
 x_50 = lean_box(0);
}
x_51 = lean_io_error_to_string(x_48);
x_52 = 3;
x_53 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_52);
x_54 = lean_array_get_size(x_37);
x_55 = lean_array_push(x_37, x_53);
x_56 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_39);
lean_ctor_set(x_56, 2, x_40);
lean_ctor_set_uint8(x_56, sizeof(void*)*3, x_38);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
if (lean_is_scalar(x_50)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_50;
 lean_ctor_set_tag(x_58, 0);
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_49);
return x_58;
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
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_30 = l_Substring_takeWhileAux___at___Lake_BuildMetadata_parse_spec__0(x_18, x_25, x_9);
x_31 = l_Substring_takeRightWhileAux___at___Lake_BuildMetadata_parse_spec__1(x_18, x_30, x_25);
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
x_41 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_42 = l_Substring_takeWhileAux___at___Lake_BuildMetadata_parse_spec__0(x_18, x_25, x_9);
x_43 = l_Substring_takeRightWhileAux___at___Lake_BuildMetadata_parse_spec__1(x_18, x_42, x_25);
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
x_4 = l_Lake_BuildMetadata_fromJson_x3f___closed__4;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
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
x_14 = lean_io_as_task(x_13, x_9, x_7);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_Lake_instDataKindFilePath;
x_18 = l_panic___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__3___closed__0;
x_19 = 0;
x_20 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*3, x_19);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = l_Lake_instDataKindFilePath;
x_24 = l_panic___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__3___closed__0;
x_25 = 0;
x_26 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set(x_26, 2, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*3, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
return x_27;
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
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__4___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__4___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
x_12 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_inputBinFile___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
x_12 = l_Lake_inputBinFile___redArg___lam__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_inputBinFile(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
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
lean_dec_ref(x_3);
x_6 = lean_io_metadata(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint64_t x_12; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_9);
lean_dec(x_8);
x_10 = l_Lake_platformTrace___closed__4;
x_11 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_11, 2, x_9);
x_12 = lean_unbox_uint64(x_4);
lean_dec(x_4);
lean_ctor_set_uint64(x_11, sizeof(void*)*3, x_12);
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_6);
x_15 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_15);
lean_dec(x_13);
x_16 = l_Lake_platformTrace___closed__4;
x_17 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_15);
x_18 = lean_unbox_uint64(x_4);
lean_dec(x_4);
lean_ctor_set_uint64(x_17, sizeof(void*)*3, x_18);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_14);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_4);
lean_dec_ref(x_1);
x_20 = !lean_is_exclusive(x_6);
if (x_20 == 0)
{
return x_6;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get(x_6, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_6);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec_ref(x_1);
x_24 = !lean_is_exclusive(x_3);
if (x_24 == 0)
{
return x_3;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_ctor_get(x_3, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_3);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
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
lean_inc_ref(x_1);
x_12 = l_Lake_BuildTrace_compute___at___Lake_inputTextFile_spec__0(x_1, x_8);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec_ref(x_11);
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
lean_dec_ref(x_1);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_io_error_to_string(x_21);
x_23 = 3;
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_23);
x_25 = lean_array_get_size(x_10);
x_26 = lean_array_push(x_10, x_24);
lean_ctor_set(x_7, 0, x_26);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_7);
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_27);
return x_12;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_12, 0);
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_12);
x_30 = lean_io_error_to_string(x_28);
x_31 = 3;
x_32 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_31);
x_33 = lean_array_get_size(x_10);
x_34 = lean_array_push(x_10, x_32);
lean_ctor_set(x_7, 0, x_34);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_7);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_29);
return x_36;
}
}
}
else
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_7, 0);
x_38 = lean_ctor_get_uint8(x_7, sizeof(void*)*3);
x_39 = lean_ctor_get(x_7, 1);
x_40 = lean_ctor_get(x_7, 2);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_37);
lean_dec(x_7);
lean_inc_ref(x_1);
x_41 = l_Lake_BuildTrace_compute___at___Lake_inputTextFile_spec__0(x_1, x_8);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec_ref(x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_45, 0, x_37);
lean_ctor_set(x_45, 1, x_42);
lean_ctor_set(x_45, 2, x_40);
lean_ctor_set_uint8(x_45, sizeof(void*)*3, x_38);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_45);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_43);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec_ref(x_1);
x_48 = lean_ctor_get(x_41, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_41, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_50 = x_41;
} else {
 lean_dec_ref(x_41);
 x_50 = lean_box(0);
}
x_51 = lean_io_error_to_string(x_48);
x_52 = 3;
x_53 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_52);
x_54 = lean_array_get_size(x_37);
x_55 = lean_array_push(x_37, x_53);
x_56 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_39);
lean_ctor_set(x_56, 2, x_40);
lean_ctor_set_uint8(x_56, sizeof(void*)*3, x_38);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
if (lean_is_scalar(x_50)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_50;
 lean_ctor_set_tag(x_58, 0);
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_49);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_30 = l_Substring_takeWhileAux___at___Lake_BuildMetadata_parse_spec__0(x_18, x_25, x_9);
x_31 = l_Substring_takeRightWhileAux___at___Lake_BuildMetadata_parse_spec__1(x_18, x_30, x_25);
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
x_41 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_42 = l_Substring_takeWhileAux___at___Lake_BuildMetadata_parse_spec__0(x_18, x_25, x_9);
x_43 = l_Substring_takeRightWhileAux___at___Lake_BuildMetadata_parse_spec__1(x_18, x_42, x_25);
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
LEAN_EXPORT lean_object* l_Lake_inputTextFile___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
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
x_14 = lean_io_as_task(x_13, x_9, x_7);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_Lake_instDataKindFilePath;
x_18 = l_panic___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__3___closed__0;
x_19 = 0;
x_20 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*3, x_19);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = l_Lake_instDataKindFilePath;
x_24 = l_panic___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__3___closed__0;
x_25 = 0;
x_26 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set(x_26, 2, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*3, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
return x_27;
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
x_12 = l_Lake_inputTextFile___redArg___lam__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_inputTextFile(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
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
x_10 = l_Lake_inputFile___redArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_Lake_inputFile(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lake_inputDir_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_array_uget(x_2, x_3);
x_13 = l_IO_FS_DirEntry_path(x_12);
lean_inc_ref(x_1);
lean_inc_ref(x_13);
x_14 = lean_apply_1(x_1, x_13);
x_15 = lean_unbox(x_14);
if (x_15 == 0)
{
lean_dec_ref(x_13);
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
lean_dec_ref(x_1);
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
static lean_object* _init_l_Array_filterMapM___at___Lake_inputDir_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lake_inputDir_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Array_filterMapM___at___Lake_inputDir_spec__0___closed__0;
x_6 = lean_nat_dec_lt(x_3, x_4);
if (x_6 == 0)
{
lean_dec_ref(x_1);
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
lean_dec_ref(x_1);
return x_5;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_3);
x_10 = lean_usize_of_nat(x_4);
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lake_inputDir_spec__0_spec__0(x_1, x_2, x_9, x_10, x_5);
return x_11;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_dec_lt(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_5 = lean_alloc_closure((void*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__2___redArg___lam__0___boxed), 2, 0);
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
x_10 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__2___redArg(x_8, x_2, x_7);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__2___redArg(x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_inputDir_spec__3(uint8_t x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
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
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_4, x_3, x_16);
if (x_1 == 0)
{
lean_object* x_26; 
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_26 = l_Lake_inputBinFile___redArg(x_15, x_5, x_6, x_7, x_8, x_9, x_11);
x_18 = x_26;
goto block_25;
}
else
{
lean_object* x_27; 
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
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
lean_dec_ref(x_18);
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
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
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
x_43 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_41, x_42, x_3, x_4, x_5, x_6, x_7, x_36, x_10);
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
x_55 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_56 = l_Substring_takeWhileAux___at___Lake_BuildMetadata_parse_spec__0(x_48, x_50, x_51);
x_57 = l_Substring_takeRightWhileAux___at___Lake_BuildMetadata_parse_spec__1(x_48, x_56, x_50);
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
x_64 = l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg___lam__1(x_49, x_62, x_3, x_4, x_5, x_6, x_7, x_47, x_46);
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
x_69 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_70 = l_Substring_takeWhileAux___at___Lake_BuildMetadata_parse_spec__0(x_48, x_50, x_51);
x_71 = l_Substring_takeRightWhileAux___at___Lake_BuildMetadata_parse_spec__1(x_48, x_70, x_50);
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
x_79 = l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg___lam__1(x_49, x_76, x_3, x_4, x_5, x_6, x_7, x_78, x_46);
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
x_81 = l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg___lam__1(x_49, x_80, x_3, x_4, x_5, x_6, x_7, x_47, x_46);
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
x_93 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_90, x_91, x_3, x_4, x_5, x_6, x_7, x_92, x_10);
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
x_108 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_109 = l_Substring_takeWhileAux___at___Lake_BuildMetadata_parse_spec__0(x_98, x_100, x_101);
x_110 = l_Substring_takeRightWhileAux___at___Lake_BuildMetadata_parse_spec__1(x_98, x_109, x_100);
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
x_118 = l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg___lam__1(x_99, x_115, x_3, x_4, x_5, x_6, x_7, x_117, x_96);
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
x_120 = l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg___lam__1(x_99, x_119, x_3, x_4, x_5, x_6, x_7, x_97, x_96);
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
x_25 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg___lam__0), 2, 1);
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
x_31 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg___lam__0), 2, 1);
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
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_12 = lean_ctor_get(x_8, 1);
x_13 = lean_ctor_get(x_8, 2);
x_14 = lean_io_read_dir(x_1, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_29; uint8_t x_30; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_17 = x_14;
} else {
 lean_dec_ref(x_14);
 x_17 = lean_box(0);
}
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_array_get_size(x_15);
x_24 = l_Array_filterMapM___at___Lake_inputDir_spec__0(x_2, x_15, x_22, x_23);
lean_dec(x_23);
lean_dec(x_15);
x_29 = lean_array_get_size(x_24);
x_30 = lean_nat_dec_eq(x_29, x_22);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_36; 
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_sub(x_29, x_31);
lean_dec(x_29);
x_36 = lean_nat_dec_le(x_22, x_32);
if (x_36 == 0)
{
lean_inc(x_32);
x_33 = x_32;
goto block_35;
}
else
{
x_33 = x_22;
goto block_35;
}
block_35:
{
uint8_t x_34; 
x_34 = lean_nat_dec_le(x_33, x_32);
if (x_34 == 0)
{
lean_dec(x_32);
lean_inc(x_33);
x_25 = x_33;
x_26 = x_33;
goto block_28;
}
else
{
x_25 = x_33;
x_26 = x_32;
goto block_28;
}
}
}
else
{
lean_dec(x_29);
x_18 = x_24;
goto block_21;
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_8);
if (lean_is_scalar(x_17)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_17;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
block_28:
{
lean_object* x_27; 
x_27 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__2___redArg(x_24, x_25, x_26);
lean_dec(x_26);
x_18 = x_27;
goto block_21;
}
}
else
{
uint8_t x_37; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc_ref(x_10);
lean_dec_ref(x_2);
x_37 = !lean_is_exclusive(x_8);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_8, 2);
lean_dec(x_38);
x_39 = lean_ctor_get(x_8, 1);
lean_dec(x_39);
x_40 = lean_ctor_get(x_8, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_14);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_14, 0);
x_43 = lean_io_error_to_string(x_42);
x_44 = 3;
x_45 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_44);
x_46 = lean_array_get_size(x_10);
x_47 = lean_array_push(x_10, x_45);
lean_ctor_set(x_8, 0, x_47);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_8);
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 0, x_48);
return x_14;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_49 = lean_ctor_get(x_14, 0);
x_50 = lean_ctor_get(x_14, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_14);
x_51 = lean_io_error_to_string(x_49);
x_52 = 3;
x_53 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_52);
x_54 = lean_array_get_size(x_10);
x_55 = lean_array_push(x_10, x_53);
lean_ctor_set(x_8, 0, x_55);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_8);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_50);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_8);
x_58 = lean_ctor_get(x_14, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_14, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_60 = x_14;
} else {
 lean_dec_ref(x_14);
 x_60 = lean_box(0);
}
x_61 = lean_io_error_to_string(x_58);
x_62 = 3;
x_63 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_62);
x_64 = lean_array_get_size(x_10);
x_65 = lean_array_push(x_10, x_63);
x_66 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_12);
lean_ctor_set(x_66, 2, x_13);
lean_ctor_set_uint8(x_66, sizeof(void*)*3, x_11);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_66);
if (lean_is_scalar(x_60)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_60;
 lean_ctor_set_tag(x_68, 0);
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_59);
return x_68;
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
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_30 = l_Substring_takeWhileAux___at___Lake_BuildMetadata_parse_spec__0(x_18, x_25, x_9);
x_31 = l_Substring_takeRightWhileAux___at___Lake_BuildMetadata_parse_spec__1(x_18, x_30, x_25);
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
x_41 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_42 = l_Substring_takeWhileAux___at___Lake_BuildMetadata_parse_spec__0(x_18, x_25, x_9);
x_43 = l_Substring_takeRightWhileAux___at___Lake_BuildMetadata_parse_spec__1(x_18, x_42, x_25);
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
static lean_object* _init_l_Lake_inputDir___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<collection>", 12, 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_array_size(x_2);
x_11 = 0;
x_12 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_inputDir_spec__3(x_1, x_10, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_17 = l_Lake_inputDir___lam__2___closed__0;
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
x_21 = l_Lake_inputDir___lam__2___closed__0;
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
x_29 = l_Lake_inputDir___lam__2___closed__0;
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
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_11 = lean_alloc_closure((void*)(l_Lake_inputDir___lam__0___boxed), 9, 2);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_3);
x_12 = lean_unsigned_to_nat(0u);
x_13 = 1;
x_14 = l_Lake_inputBinFile___redArg___closed__2;
x_15 = lean_box(x_13);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_16 = lean_alloc_closure((void*)(l_Lake_inputDir___lam__1___boxed), 10, 9);
lean_closure_set(x_16, 0, x_11);
lean_closure_set(x_16, 1, x_15);
lean_closure_set(x_16, 2, x_4);
lean_closure_set(x_16, 3, x_5);
lean_closure_set(x_16, 4, x_6);
lean_closure_set(x_16, 5, x_7);
lean_closure_set(x_16, 6, x_8);
lean_closure_set(x_16, 7, x_14);
lean_closure_set(x_16, 8, x_12);
x_17 = lean_io_as_task(x_16, x_12, x_10);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_box(x_2);
x_21 = lean_alloc_closure((void*)(l_Lake_inputDir___lam__2___boxed), 9, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_box(0);
x_23 = l_panic___at___IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1_spec__3___closed__0;
x_24 = 0;
x_25 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*3, x_24);
x_26 = l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg(x_25, x_21, x_12, x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
return x_26;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lake_inputDir_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lake_inputDir_spec__0_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lake_inputDir_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_filterMapM___at___Lake_inputDir_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__2___redArg___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__2___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___Lake_inputDir_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_inputDir_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_inputDir_spec__3(x_12, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
x_13 = l_Lake_Job_bindM___at___Lake_inputDir_spec__4___redArg(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_inputDir_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
x_14 = l_Lake_Job_bindM___at___Lake_inputDir_spec__4(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_inputDir___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
x_12 = l_Lake_inputDir___lam__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
x_11 = l_Lake_inputDir___lam__2(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_inputDir___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
x_12 = l_Lake_inputDir(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_10, 0);
x_43 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
x_44 = lean_ctor_get(x_10, 1);
x_45 = lean_ctor_get(x_10, 2);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_42);
lean_dec(x_10);
x_46 = l_Lake_compileO(x_1, x_2, x_3, x_4, x_42, x_11);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
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
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_52 = x_47;
} else {
 lean_dec_ref(x_47);
 x_52 = lean_box(0);
}
x_53 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_44);
lean_ctor_set(x_53, 2, x_45);
lean_ctor_set_uint8(x_53, sizeof(void*)*3, x_43);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_53);
if (lean_is_scalar(x_49)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_49;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_48);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_56 = lean_ctor_get(x_46, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_57 = x_46;
} else {
 lean_dec_ref(x_46);
 x_57 = lean_box(0);
}
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
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_44);
lean_ctor_set(x_61, 2, x_45);
lean_ctor_set_uint8(x_61, sizeof(void*)*3, x_43);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_61);
if (lean_is_scalar(x_57)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_57;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_56);
return x_63;
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
LEAN_EXPORT lean_object* l_Lake_buildO___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; uint64_t x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
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
x_73 = l_Lake_platformTrace___closed__1;
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_array_get_size(x_1);
x_76 = lean_nat_dec_lt(x_74, x_75);
if (x_76 == 0)
{
lean_dec(x_75);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_24 = x_73;
goto block_72;
}
else
{
uint8_t x_77; 
x_77 = lean_nat_dec_le(x_75, x_75);
if (x_77 == 0)
{
lean_dec(x_75);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_24 = x_73;
goto block_72;
}
else
{
size_t x_78; size_t x_79; lean_object* x_80; lean_object* x_81; uint64_t x_82; 
x_78 = 0;
x_79 = lean_usize_of_nat(x_75);
lean_dec(x_75);
x_80 = l_Lake_buildO___lam__2___boxed__const__1;
lean_inc_ref(x_1);
x_81 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_7, x_8, x_1, x_78, x_79, x_80);
x_82 = lean_unbox_uint64(x_81);
lean_dec(x_81);
x_24 = x_82;
goto block_72;
}
}
block_72:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
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
lean_dec_ref(x_36);
x_40 = lean_ctor_get(x_37, 0);
lean_inc(x_40);
lean_dec_ref(x_37);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_38, 1);
x_43 = l_Lake_BuildTrace_mix(x_42, x_40);
lean_ctor_set(x_38, 1, x_43);
x_44 = l_Array_append___redArg(x_4, x_1);
lean_dec_ref(x_1);
lean_inc_ref(x_5);
x_45 = lean_alloc_closure((void*)(l_Lake_buildO___lam__1___boxed), 11, 4);
lean_closure_set(x_45, 0, x_5);
lean_closure_set(x_45, 1, x_9);
lean_closure_set(x_45, 2, x_44);
lean_closure_set(x_45, 3, x_6);
x_46 = 0;
x_47 = l_Lake_buildO___lam__2___closed__2;
x_48 = l_Lake_buildArtifactUnlessUpToDate(x_5, x_45, x_46, x_47, x_46, x_46, x_10, x_11, x_12, x_13, x_14, x_38, x_39);
return x_48;
}
else
{
lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; 
x_49 = lean_ctor_get(x_38, 0);
x_50 = lean_ctor_get_uint8(x_38, sizeof(void*)*3);
x_51 = lean_ctor_get(x_38, 1);
x_52 = lean_ctor_get(x_38, 2);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_49);
lean_dec(x_38);
x_53 = l_Lake_BuildTrace_mix(x_51, x_40);
x_54 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*3, x_50);
x_55 = l_Array_append___redArg(x_4, x_1);
lean_dec_ref(x_1);
lean_inc_ref(x_5);
x_56 = lean_alloc_closure((void*)(l_Lake_buildO___lam__1___boxed), 11, 4);
lean_closure_set(x_56, 0, x_5);
lean_closure_set(x_56, 1, x_9);
lean_closure_set(x_56, 2, x_55);
lean_closure_set(x_56, 3, x_6);
x_57 = 0;
x_58 = l_Lake_buildO___lam__2___closed__2;
x_59 = l_Lake_buildArtifactUnlessUpToDate(x_5, x_56, x_57, x_58, x_57, x_57, x_10, x_11, x_12, x_13, x_14, x_54, x_39);
return x_59;
}
}
else
{
uint8_t x_60; 
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
x_60 = !lean_is_exclusive(x_36);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_36, 0);
lean_dec(x_61);
x_62 = !lean_is_exclusive(x_37);
if (x_62 == 0)
{
return x_36;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_37, 0);
x_64 = lean_ctor_get(x_37, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_37);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_36, 0, x_65);
return x_36;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = lean_ctor_get(x_36, 1);
lean_inc(x_66);
lean_dec(x_36);
x_67 = lean_ctor_get(x_37, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_37, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_69 = x_37;
} else {
 lean_dec_ref(x_37);
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
return x_71;
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
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
x_20 = 0;
x_21 = l_Lake_Job_mapM___redArg(x_15, x_2, x_18, x_19, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
x_12 = l_Lake_buildO___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
return x_12;
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
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_17 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_15, x_16, x_3, x_4, x_5, x_6, x_7, x_10, x_9);
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
x_36 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_37 = l_Substring_takeWhileAux___at___Lake_BuildMetadata_parse_spec__0(x_24, x_31, x_32);
x_38 = l_Substring_takeRightWhileAux___at___Lake_BuildMetadata_parse_spec__1(x_24, x_37, x_31);
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
x_48 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_49 = l_Substring_takeWhileAux___at___Lake_BuildMetadata_parse_spec__0(x_24, x_31, x_32);
x_50 = l_Substring_takeRightWhileAux___at___Lake_BuildMetadata_parse_spec__1(x_24, x_49, x_31);
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
x_77 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_74, x_75, x_3, x_4, x_5, x_6, x_7, x_76, x_9);
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
x_99 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_100 = l_Substring_takeWhileAux___at___Lake_BuildMetadata_parse_spec__0(x_84, x_91, x_92);
x_101 = l_Substring_takeRightWhileAux___at___Lake_BuildMetadata_parse_spec__1(x_84, x_100, x_91);
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
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_15 = lean_alloc_closure((void*)(l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3___redArg___lam__0), 9, 7);
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
x_27 = lean_alloc_closure((void*)(l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3___redArg___lam__0), 9, 7);
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
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
lean_object* x_64; 
x_64 = lean_ctor_get(x_20, 4);
lean_inc_ref(x_64);
x_21 = x_64;
goto block_63;
}
else
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_5, 0);
lean_inc(x_65);
lean_dec_ref(x_5);
x_21 = x_65;
goto block_63;
}
block_63:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
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
x_29 = l_Lake_compileO(x_3, x_4, x_28, x_22, x_15, x_12);
lean_dec_ref(x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_30, 1);
if (lean_is_scalar(x_19)) {
 x_35 = lean_alloc_ctor(0, 3, 1);
} else {
 x_35 = x_19;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_17);
lean_ctor_set(x_35, 2, x_18);
lean_ctor_set_uint8(x_35, sizeof(void*)*3, x_16);
lean_ctor_set(x_30, 1, x_35);
return x_29;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
if (lean_is_scalar(x_19)) {
 x_38 = lean_alloc_ctor(0, 3, 1);
} else {
 x_38 = x_19;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_17);
lean_ctor_set(x_38, 2, x_18);
lean_ctor_set_uint8(x_38, sizeof(void*)*3, x_16);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_29, 0, x_39);
return x_29;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_29, 1);
lean_inc(x_40);
lean_dec(x_29);
x_41 = lean_ctor_get(x_30, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_30, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_43 = x_30;
} else {
 lean_dec_ref(x_30);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_19)) {
 x_44 = lean_alloc_ctor(0, 3, 1);
} else {
 x_44 = x_19;
}
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_17);
lean_ctor_set(x_44, 2, x_18);
lean_ctor_set_uint8(x_44, sizeof(void*)*3, x_16);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_40);
return x_46;
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_29);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_29, 0);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_30);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_30, 1);
if (lean_is_scalar(x_19)) {
 x_51 = lean_alloc_ctor(0, 3, 1);
} else {
 x_51 = x_19;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_17);
lean_ctor_set(x_51, 2, x_18);
lean_ctor_set_uint8(x_51, sizeof(void*)*3, x_16);
lean_ctor_set(x_30, 1, x_51);
return x_29;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_30, 0);
x_53 = lean_ctor_get(x_30, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_30);
if (lean_is_scalar(x_19)) {
 x_54 = lean_alloc_ctor(0, 3, 1);
} else {
 x_54 = x_19;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_17);
lean_ctor_set(x_54, 2, x_18);
lean_ctor_set_uint8(x_54, sizeof(void*)*3, x_16);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_29, 0, x_55);
return x_29;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_29, 1);
lean_inc(x_56);
lean_dec(x_29);
x_57 = lean_ctor_get(x_30, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_30, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_59 = x_30;
} else {
 lean_dec_ref(x_30);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_19)) {
 x_60 = lean_alloc_ctor(0, 3, 1);
} else {
 x_60 = x_19;
}
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_17);
lean_ctor_set(x_60, 2, x_18);
lean_ctor_set_uint8(x_60, sizeof(void*)*3, x_16);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_57);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_56);
return x_62;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint64_t x_21; uint64_t x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
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
x_39 = l_Lake_platformTrace___closed__1;
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_array_get_size(x_2);
x_42 = lean_nat_dec_lt(x_40, x_41);
if (x_42 == 0)
{
lean_dec(x_41);
x_21 = x_39;
goto block_38;
}
else
{
uint8_t x_43; 
x_43 = lean_nat_dec_le(x_41, x_41);
if (x_43 == 0)
{
lean_dec(x_41);
x_21 = x_39;
goto block_38;
}
else
{
size_t x_44; size_t x_45; uint64_t x_46; 
x_44 = 0;
x_45 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_46 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_buildLeanO_spec__2(x_2, x_44, x_45, x_39);
x_21 = x_46;
goto block_38;
}
}
block_38:
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
x_37 = l_Lake_buildArtifactUnlessUpToDate(x_3, x_19, x_35, x_36, x_35, x_35, x_6, x_7, x_8, x_9, x_10, x_34, x_12);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_alloc_closure((void*)(l_Lake_buildLeanO___lam__1), 12, 4);
lean_closure_set(x_13, 0, x_3);
lean_closure_set(x_13, 1, x_4);
lean_closure_set(x_13, 2, x_1);
lean_closure_set(x_13, 3, x_5);
x_14 = lean_unsigned_to_nat(0u);
x_15 = 0;
x_16 = l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3___redArg(x_2, x_13, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
x_13 = l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3___redArg(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
x_14 = l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_13, 11);
lean_inc_ref(x_16);
lean_dec_ref(x_13);
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
lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_9, 0);
x_46 = lean_ctor_get_uint8(x_9, sizeof(void*)*3);
x_47 = lean_ctor_get(x_9, 1);
x_48 = lean_ctor_get(x_9, 2);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_45);
lean_dec(x_9);
x_49 = lean_ctor_get(x_13, 11);
lean_inc_ref(x_49);
lean_dec_ref(x_13);
x_50 = l_Lake_compileStaticLib(x_1, x_2, x_49, x_3, x_45, x_10);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
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
x_54 = lean_ctor_get(x_51, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_56 = x_51;
} else {
 lean_dec_ref(x_51);
 x_56 = lean_box(0);
}
x_57 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_47);
lean_ctor_set(x_57, 2, x_48);
lean_ctor_set_uint8(x_57, sizeof(void*)*3, x_46);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_54);
lean_ctor_set(x_58, 1, x_57);
if (lean_is_scalar(x_53)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_53;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_52);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_60 = lean_ctor_get(x_50, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_61 = x_50;
} else {
 lean_dec_ref(x_50);
 x_61 = lean_box(0);
}
x_62 = lean_ctor_get(x_51, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_51, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_64 = x_51;
} else {
 lean_dec_ref(x_51);
 x_64 = lean_box(0);
}
x_65 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_47);
lean_ctor_set(x_65, 2, x_48);
lean_ctor_set_uint8(x_65, sizeof(void*)*3, x_46);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_62);
lean_ctor_set(x_66, 1, x_65);
if (lean_is_scalar(x_61)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_61;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_60);
return x_67;
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
x_16 = l_Lake_buildArtifactUnlessUpToDate(x_1, x_12, x_13, x_14, x_15, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_16;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_11 = lean_box(x_3);
x_12 = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lam__1___boxed), 10, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
x_13 = l_Lake_buildStaticLib___closed__0;
x_14 = l_Lake_Job_collectArray___redArg(x_2, x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = 0;
x_17 = l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3___redArg(x_14, x_12, x_15, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
x_12 = l_Lake_buildStaticLib___lam__0(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_12 = l_Lake_buildStaticLib___lam__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
x_12 = l_Lake_buildStaticLib(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_3 = l_Array_filterMapM___at___Lake_inputDir_spec__0___closed__0;
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
x_42 = lean_nat_add(x_40, x_41);
lean_dec(x_41);
lean_dec(x_40);
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
lean_ctor_set(x_44, 3, x_39);
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
x_39 = x_48;
x_40 = x_49;
x_41 = x_50;
goto block_45;
}
else
{
lean_object* x_51; 
x_51 = lean_unsigned_to_nat(0u);
x_39 = x_48;
x_40 = x_49;
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
x_16 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__0(x_1, x_14, x_15, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2;
x_21 = l_Lake_formatCycle___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(x_17);
x_22 = lean_string_append(x_20, x_21);
lean_dec_ref(x_21);
x_23 = 3;
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_23);
x_25 = lean_array_get_size(x_19);
x_26 = lean_array_push(x_19, x_24);
lean_ctor_set(x_2, 0, x_26);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_2);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_3);
return x_28;
}
else
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_31 = lean_ctor_get(x_2, 1);
x_32 = lean_ctor_get(x_2, 2);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_29);
lean_dec(x_2);
x_33 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__2;
x_34 = l_Lake_formatCycle___at_____private_Lake_Build_Common_0__Lake_mkLinkOrder_spec__1(x_17);
x_35 = lean_string_append(x_33, x_34);
lean_dec_ref(x_34);
x_36 = 3;
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_36);
x_38 = lean_array_get_size(x_29);
x_39 = lean_array_push(x_29, x_37);
x_40 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_31);
lean_ctor_set(x_40, 2, x_32);
lean_ctor_set_uint8(x_40, sizeof(void*)*3, x_30);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_3);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_16, 0);
lean_inc(x_43);
lean_dec_ref(x_16);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_4 = x_44;
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
x_4 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_mkLinkOrder___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
x_17 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_15, x_16, x_3, x_4, x_5, x_6, x_7, x_10, x_9);
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
x_36 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_37 = l_Substring_takeWhileAux___at___Lake_BuildMetadata_parse_spec__0(x_24, x_31, x_32);
x_38 = l_Substring_takeRightWhileAux___at___Lake_BuildMetadata_parse_spec__1(x_24, x_37, x_31);
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
x_48 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_49 = l_Substring_takeWhileAux___at___Lake_BuildMetadata_parse_spec__0(x_24, x_31, x_32);
x_50 = l_Substring_takeRightWhileAux___at___Lake_BuildMetadata_parse_spec__1(x_24, x_49, x_31);
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
x_77 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_74, x_75, x_3, x_4, x_5, x_6, x_7, x_76, x_9);
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
x_99 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_100 = l_Substring_takeWhileAux___at___Lake_BuildMetadata_parse_spec__0(x_84, x_91, x_92);
x_101 = l_Substring_takeRightWhileAux___at___Lake_BuildMetadata_parse_spec__1(x_84, x_100, x_91);
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
x_43 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_41, x_42, x_3, x_4, x_5, x_6, x_7, x_36, x_10);
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
x_55 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_56 = l_Substring_takeWhileAux___at___Lake_BuildMetadata_parse_spec__0(x_48, x_50, x_51);
x_57 = l_Substring_takeRightWhileAux___at___Lake_BuildMetadata_parse_spec__1(x_48, x_56, x_50);
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
x_64 = l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__1(x_49, x_62, x_3, x_4, x_5, x_6, x_7, x_47, x_46);
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
x_69 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_70 = l_Substring_takeWhileAux___at___Lake_BuildMetadata_parse_spec__0(x_48, x_50, x_51);
x_71 = l_Substring_takeRightWhileAux___at___Lake_BuildMetadata_parse_spec__1(x_48, x_70, x_50);
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
x_79 = l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__1(x_49, x_76, x_3, x_4, x_5, x_6, x_7, x_78, x_46);
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
x_81 = l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__1(x_49, x_80, x_3, x_4, x_5, x_6, x_7, x_47, x_46);
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
x_93 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_90, x_91, x_3, x_4, x_5, x_6, x_7, x_92, x_10);
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
x_108 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_109 = l_Substring_takeWhileAux___at___Lake_BuildMetadata_parse_spec__0(x_98, x_100, x_101);
x_110 = l_Substring_takeRightWhileAux___at___Lake_BuildMetadata_parse_spec__1(x_98, x_109, x_100);
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
x_118 = l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__1(x_99, x_115, x_3, x_4, x_5, x_6, x_7, x_117, x_96);
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
x_120 = l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__1(x_99, x_119, x_3, x_4, x_5, x_6, x_7, x_97, x_96);
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
x_25 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__0), 2, 1);
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
x_31 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__0), 2, 1);
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
lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_47 = lean_ctor_get(x_12, 0);
x_48 = lean_ctor_get_uint8(x_12, sizeof(void*)*3);
x_49 = lean_ctor_get(x_12, 1);
x_50 = lean_ctor_get(x_12, 2);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_47);
lean_dec(x_12);
x_51 = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(x_1, x_6);
x_52 = l_Array_append___redArg(x_51, x_2);
x_53 = l_Array_append___redArg(x_52, x_3);
x_54 = l_Lake_compileSharedLib(x_4, x_53, x_5, x_47, x_13);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
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
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_55, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_60 = x_55;
} else {
 lean_dec_ref(x_55);
 x_60 = lean_box(0);
}
x_61 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_49);
lean_ctor_set(x_61, 2, x_50);
lean_ctor_set_uint8(x_61, sizeof(void*)*3, x_48);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_61);
if (lean_is_scalar(x_57)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_57;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_56);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_64 = lean_ctor_get(x_54, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_65 = x_54;
} else {
 lean_dec_ref(x_54);
 x_65 = lean_box(0);
}
x_66 = lean_ctor_get(x_55, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_55, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_68 = x_55;
} else {
 lean_dec_ref(x_55);
 x_68 = lean_box(0);
}
x_69 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_49);
lean_ctor_set(x_69, 2, x_50);
lean_ctor_set_uint8(x_69, sizeof(void*)*3, x_48);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_66);
lean_ctor_set(x_70, 1, x_69);
if (lean_is_scalar(x_65)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_65;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_64);
return x_71;
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
lean_dec_ref(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec_ref(x_15);
x_19 = lean_apply_8(x_3, x_17, x_5, x_6, x_7, x_8, x_9, x_18, x_16);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
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
static lean_object* _init_l_Lake_buildSharedLib___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_sharedLibExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint64_t x_16; uint64_t x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_175 = l_Lake_platformTrace___closed__1;
x_176 = lean_unsigned_to_nat(0u);
x_177 = lean_array_get_size(x_1);
x_178 = lean_nat_dec_lt(x_176, x_177);
if (x_178 == 0)
{
lean_dec(x_177);
x_16 = x_175;
goto block_174;
}
else
{
uint8_t x_179; 
x_179 = lean_nat_dec_le(x_177, x_177);
if (x_179 == 0)
{
lean_dec(x_177);
x_16 = x_175;
goto block_174;
}
else
{
size_t x_180; size_t x_181; uint64_t x_182; 
x_180 = 0;
x_181 = lean_usize_of_nat(x_177);
lean_dec(x_177);
x_182 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_buildLeanO_spec__2(x_1, x_180, x_181, x_175);
x_16 = x_182;
goto block_174;
}
}
block_174:
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
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
x_32 = lean_apply_7(x_2, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec_ref(x_32);
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec_ref(x_33);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_34, 1);
x_39 = lean_box(x_3);
lean_inc_ref(x_8);
x_40 = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__1___boxed), 11, 4);
lean_closure_set(x_40, 0, x_39);
lean_closure_set(x_40, 1, x_25);
lean_closure_set(x_40, 2, x_4);
lean_closure_set(x_40, 3, x_8);
x_41 = l_Lake_BuildTrace_mix(x_38, x_36);
lean_ctor_set(x_34, 1, x_41);
x_42 = 1;
x_43 = 0;
x_44 = l_Lake_buildSharedLib___lam__2___closed__0;
x_45 = l_Lake_buildArtifactUnlessUpToDate(x_5, x_40, x_43, x_44, x_42, x_43, x_9, x_10, x_11, x_12, x_13, x_34, x_35);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_45);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_45, 0);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_46, 0);
x_51 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_6);
lean_ctor_set(x_51, 2, x_8);
lean_ctor_set_uint8(x_51, sizeof(void*)*3, x_7);
lean_ctor_set(x_46, 0, x_51);
return x_45;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_46, 0);
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_46);
x_54 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_6);
lean_ctor_set(x_54, 2, x_8);
lean_ctor_set_uint8(x_54, sizeof(void*)*3, x_7);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
lean_ctor_set(x_45, 0, x_55);
return x_45;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_45, 1);
lean_inc(x_56);
lean_dec(x_45);
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
x_60 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_6);
lean_ctor_set(x_60, 2, x_8);
lean_ctor_set_uint8(x_60, sizeof(void*)*3, x_7);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_56);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_63 = !lean_is_exclusive(x_45);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_45, 0);
lean_dec(x_64);
x_65 = !lean_is_exclusive(x_46);
if (x_65 == 0)
{
return x_45;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_46, 0);
x_67 = lean_ctor_get(x_46, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_46);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_45, 0, x_68);
return x_45;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_45, 1);
lean_inc(x_69);
lean_dec(x_45);
x_70 = lean_ctor_get(x_46, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_46, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_72 = x_46;
} else {
 lean_dec_ref(x_46);
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
else
{
lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_75 = lean_ctor_get(x_34, 0);
x_76 = lean_ctor_get_uint8(x_34, sizeof(void*)*3);
x_77 = lean_ctor_get(x_34, 1);
x_78 = lean_ctor_get(x_34, 2);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_75);
lean_dec(x_34);
x_79 = lean_box(x_3);
lean_inc_ref(x_8);
x_80 = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__1___boxed), 11, 4);
lean_closure_set(x_80, 0, x_79);
lean_closure_set(x_80, 1, x_25);
lean_closure_set(x_80, 2, x_4);
lean_closure_set(x_80, 3, x_8);
x_81 = l_Lake_BuildTrace_mix(x_77, x_36);
x_82 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_82, 0, x_75);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_82, 2, x_78);
lean_ctor_set_uint8(x_82, sizeof(void*)*3, x_76);
x_83 = 1;
x_84 = 0;
x_85 = l_Lake_buildSharedLib___lam__2___closed__0;
x_86 = l_Lake_buildArtifactUnlessUpToDate(x_5, x_80, x_84, x_85, x_83, x_84, x_9, x_10, x_11, x_12, x_13, x_82, x_35);
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
lean_ctor_set(x_93, 1, x_6);
lean_ctor_set(x_93, 2, x_8);
lean_ctor_set_uint8(x_93, sizeof(void*)*3, x_7);
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
lean_dec_ref(x_8);
lean_dec_ref(x_6);
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
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_103 = !lean_is_exclusive(x_32);
if (x_103 == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_ctor_get(x_32, 0);
lean_dec(x_104);
x_105 = !lean_is_exclusive(x_33);
if (x_105 == 0)
{
return x_32;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_33, 0);
x_107 = lean_ctor_get(x_33, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_33);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set(x_32, 0, x_108);
return x_32;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_109 = lean_ctor_get(x_32, 1);
lean_inc(x_109);
lean_dec(x_32);
x_110 = lean_ctor_get(x_33, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_33, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_112 = x_33;
} else {
 lean_dec_ref(x_33);
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
x_116 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
x_117 = lean_ctor_get(x_14, 1);
x_118 = lean_ctor_get(x_14, 2);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_115);
lean_dec(x_14);
x_119 = l_Lake_buildO___lam__2___closed__0;
x_120 = l_Lake_buildO___lam__2___closed__1;
x_121 = lean_array_to_list(x_1);
x_122 = l_List_toString___at___Lake_buildLeanO_spec__0(x_121);
lean_dec(x_121);
x_123 = lean_string_append(x_120, x_122);
lean_dec_ref(x_122);
x_124 = lean_string_append(x_119, x_123);
lean_dec_ref(x_123);
x_125 = lean_unsigned_to_nat(0u);
x_126 = l_Lake_platformTrace___closed__4;
x_127 = l_Lake_platformTrace___closed__6;
x_128 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_128, 0, x_124);
lean_ctor_set(x_128, 1, x_126);
lean_ctor_set(x_128, 2, x_127);
lean_ctor_set_uint64(x_128, sizeof(void*)*3, x_16);
x_129 = l_Lake_BuildTrace_mix(x_117, x_128);
x_130 = l_Lake_platformTrace;
x_131 = l_Lake_BuildTrace_mix(x_129, x_130);
x_132 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_132, 0, x_115);
lean_ctor_set(x_132, 1, x_131);
lean_ctor_set(x_132, 2, x_118);
lean_ctor_set_uint8(x_132, sizeof(void*)*3, x_116);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_133 = lean_apply_7(x_2, x_9, x_10, x_11, x_12, x_13, x_132, x_15);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
lean_dec_ref(x_133);
x_137 = lean_ctor_get(x_134, 0);
lean_inc(x_137);
lean_dec_ref(x_134);
x_138 = lean_ctor_get(x_135, 0);
lean_inc_ref(x_138);
x_139 = lean_ctor_get_uint8(x_135, sizeof(void*)*3);
x_140 = lean_ctor_get(x_135, 1);
lean_inc_ref(x_140);
x_141 = lean_ctor_get(x_135, 2);
lean_inc(x_141);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 lean_ctor_release(x_135, 2);
 x_142 = x_135;
} else {
 lean_dec_ref(x_135);
 x_142 = lean_box(0);
}
x_143 = lean_box(x_3);
lean_inc_ref(x_8);
x_144 = lean_alloc_closure((void*)(l_Lake_buildSharedLib___lam__1___boxed), 11, 4);
lean_closure_set(x_144, 0, x_143);
lean_closure_set(x_144, 1, x_125);
lean_closure_set(x_144, 2, x_4);
lean_closure_set(x_144, 3, x_8);
x_145 = l_Lake_BuildTrace_mix(x_140, x_137);
if (lean_is_scalar(x_142)) {
 x_146 = lean_alloc_ctor(0, 3, 1);
} else {
 x_146 = x_142;
}
lean_ctor_set(x_146, 0, x_138);
lean_ctor_set(x_146, 1, x_145);
lean_ctor_set(x_146, 2, x_141);
lean_ctor_set_uint8(x_146, sizeof(void*)*3, x_139);
x_147 = 1;
x_148 = 0;
x_149 = l_Lake_buildSharedLib___lam__2___closed__0;
x_150 = l_Lake_buildArtifactUnlessUpToDate(x_5, x_144, x_148, x_149, x_147, x_148, x_9, x_10, x_11, x_12, x_13, x_146, x_136);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
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
x_154 = lean_ctor_get(x_151, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_151, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_156 = x_151;
} else {
 lean_dec_ref(x_151);
 x_156 = lean_box(0);
}
x_157 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_6);
lean_ctor_set(x_157, 2, x_8);
lean_ctor_set_uint8(x_157, sizeof(void*)*3, x_7);
if (lean_is_scalar(x_156)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_156;
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_155);
if (lean_is_scalar(x_153)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_153;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_152);
return x_159;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_160 = lean_ctor_get(x_150, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_161 = x_150;
} else {
 lean_dec_ref(x_150);
 x_161 = lean_box(0);
}
x_162 = lean_ctor_get(x_151, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_151, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_164 = x_151;
} else {
 lean_dec_ref(x_151);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_163);
if (lean_is_scalar(x_161)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_161;
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_160);
return x_166;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_167 = lean_ctor_get(x_133, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_168 = x_133;
} else {
 lean_dec_ref(x_133);
 x_168 = lean_box(0);
}
x_169 = lean_ctor_get(x_134, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_134, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_171 = x_134;
} else {
 lean_dec_ref(x_134);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
if (lean_is_scalar(x_168)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_168;
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_167);
return x_173;
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
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; 
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
x_27 = l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___redArg(x_24, x_22, x_25, x_26, x_11, x_12, x_13, x_14, x_15, x_18, x_17);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_16);
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
lean_ctor_set(x_33, 1, x_16);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
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
x_25 = l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg(x_22, x_20, x_23, x_24, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
x_13 = l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___redArg(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
x_14 = l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
x_13 = l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
x_14 = l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildSharedLib___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lake_buildSharedLib___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
x_13 = l_Lake_buildSharedLib___lam__1(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_18 = l_Lake_buildSharedLib___lam__2(x_1, x_2, x_16, x_4, x_5, x_6, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
x_20 = l_Lake_buildSharedLib___lam__3(x_1, x_2, x_3, x_4, x_5, x_18, x_7, x_19, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
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
x_20 = l_Lake_buildSharedLib(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18, x_19, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
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
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
lean_object* x_90; 
x_90 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg___closed__0;
x_17 = x_90;
x_18 = x_12;
x_19 = x_13;
goto block_89;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(x_6, x_12, x_13);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec_ref(x_91);
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec_ref(x_92);
x_17 = x_94;
x_18 = x_95;
x_19 = x_93;
goto block_89;
}
else
{
uint8_t x_96; 
lean_dec_ref(x_16);
lean_dec_ref(x_4);
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
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
x_32 = l_Lake_compileSharedLib(x_4, x_31, x_21, x_24, x_19);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_32, 0);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_33, 1);
lean_ctor_set(x_18, 0, x_37);
lean_ctor_set(x_33, 1, x_18);
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_33, 0);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_33);
lean_ctor_set(x_18, 0, x_39);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_18);
lean_ctor_set(x_32, 0, x_40);
return x_32;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_32, 1);
lean_inc(x_41);
lean_dec(x_32);
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_44 = x_33;
} else {
 lean_dec_ref(x_33);
 x_44 = lean_box(0);
}
lean_ctor_set(x_18, 0, x_43);
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_18);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
return x_46;
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_32);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_32, 0);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_33);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_33, 1);
lean_ctor_set(x_18, 0, x_50);
lean_ctor_set(x_33, 1, x_18);
return x_32;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_33, 0);
x_52 = lean_ctor_get(x_33, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_33);
lean_ctor_set(x_18, 0, x_52);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_18);
lean_ctor_set(x_32, 0, x_53);
return x_32;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_32, 1);
lean_inc(x_54);
lean_dec(x_32);
x_55 = lean_ctor_get(x_33, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_33, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_57 = x_33;
} else {
 lean_dec_ref(x_33);
 x_57 = lean_box(0);
}
lean_ctor_set(x_18, 0, x_56);
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_18);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_54);
return x_59;
}
}
}
else
{
lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_60 = lean_ctor_get(x_18, 0);
x_61 = lean_ctor_get_uint8(x_18, sizeof(void*)*3);
x_62 = lean_ctor_get(x_18, 1);
x_63 = lean_ctor_get(x_18, 2);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_60);
lean_dec(x_18);
x_64 = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(x_1, x_17);
lean_dec_ref(x_17);
x_65 = l_Array_append___redArg(x_64, x_2);
x_66 = l_Array_append___redArg(x_65, x_3);
x_67 = l_Lake_buildLeanSharedLib___lam__0___closed__0;
x_68 = lean_array_push(x_67, x_20);
x_69 = l_Array_append___redArg(x_66, x_68);
lean_dec_ref(x_68);
x_70 = l_Array_append___redArg(x_69, x_22);
lean_dec_ref(x_22);
x_71 = l_Lake_compileSharedLib(x_4, x_70, x_21, x_60, x_19);
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
x_78 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_62);
lean_ctor_set(x_78, 2, x_63);
lean_ctor_set_uint8(x_78, sizeof(void*)*3, x_61);
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
x_86 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_62);
lean_ctor_set(x_86, 2, x_63);
lean_ctor_set_uint8(x_86, sizeof(void*)*3, x_61);
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
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; uint64_t x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
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
x_73 = l_Lake_platformTrace___closed__1;
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_array_get_size(x_3);
x_76 = lean_nat_dec_lt(x_74, x_75);
if (x_76 == 0)
{
lean_dec(x_75);
x_25 = x_73;
goto block_72;
}
else
{
uint8_t x_77; 
x_77 = lean_nat_dec_le(x_75, x_75);
if (x_77 == 0)
{
lean_dec(x_75);
x_25 = x_73;
goto block_72;
}
else
{
size_t x_78; size_t x_79; uint64_t x_80; 
x_78 = 0;
x_79 = lean_usize_of_nat(x_75);
lean_dec(x_75);
x_80 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_buildLeanO_spec__2(x_3, x_78, x_79, x_73);
x_25 = x_80;
goto block_72;
}
}
block_72:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
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
x_42 = l_Lake_buildArtifactUnlessUpToDate(x_4, x_23, x_39, x_40, x_41, x_39, x_9, x_10, x_11, x_12, x_13, x_38, x_15);
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
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_43, 0);
x_48 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_6);
lean_ctor_set(x_48, 2, x_8);
lean_ctor_set_uint8(x_48, sizeof(void*)*3, x_7);
lean_ctor_set(x_43, 0, x_48);
return x_42;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_43, 0);
x_50 = lean_ctor_get(x_43, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_43);
x_51 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_6);
lean_ctor_set(x_51, 2, x_8);
lean_ctor_set_uint8(x_51, sizeof(void*)*3, x_7);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
lean_ctor_set(x_42, 0, x_52);
return x_42;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_42, 1);
lean_inc(x_53);
lean_dec(x_42);
x_54 = lean_ctor_get(x_43, 0);
lean_inc(x_54);
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
x_57 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_6);
lean_ctor_set(x_57, 2, x_8);
lean_ctor_set_uint8(x_57, sizeof(void*)*3, x_7);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_53);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec_ref(x_8);
lean_dec_ref(x_6);
x_60 = !lean_is_exclusive(x_42);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_42, 0);
lean_dec(x_61);
x_62 = !lean_is_exclusive(x_43);
if (x_62 == 0)
{
return x_42;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_43, 0);
x_64 = lean_ctor_get(x_43, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_43);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_42, 0, x_65);
return x_42;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = lean_ctor_get(x_42, 1);
lean_inc(x_66);
lean_dec(x_42);
x_67 = lean_ctor_get(x_43, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_43, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_69 = x_43;
} else {
 lean_dec_ref(x_43);
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
return x_71;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; 
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
x_24 = l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0___redArg(x_21, x_19, x_22, x_23, x_9, x_10, x_11, x_12, x_13, x_16, x_15);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_14);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_24);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_14);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
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
x_23 = l_Lake_Job_bindM___at___Lake_buildSharedLib_spec__1___redArg(x_20, x_18, x_21, x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_5);
x_15 = l_Lake_buildLeanSharedLib___lam__0(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
x_18 = l_Lake_buildLeanSharedLib___lam__1(x_1, x_2, x_3, x_4, x_16, x_6, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_4);
x_17 = lean_unbox(x_6);
x_18 = l_Lake_buildLeanSharedLib___lam__2(x_1, x_2, x_3, x_16, x_5, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
x_18 = l_Lake_buildLeanSharedLib(x_1, x_2, x_3, x_4, x_5, x_6, x_16, x_17, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
x_43 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_41, x_42, x_3, x_4, x_5, x_6, x_7, x_36, x_10);
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
x_55 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_56 = l_Substring_takeWhileAux___at___Lake_BuildMetadata_parse_spec__0(x_48, x_50, x_51);
x_57 = l_Substring_takeRightWhileAux___at___Lake_BuildMetadata_parse_spec__1(x_48, x_56, x_50);
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
x_64 = l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__1(x_49, x_62, x_3, x_4, x_5, x_6, x_7, x_47, x_46);
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
x_69 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_70 = l_Substring_takeWhileAux___at___Lake_BuildMetadata_parse_spec__0(x_48, x_50, x_51);
x_71 = l_Substring_takeRightWhileAux___at___Lake_BuildMetadata_parse_spec__1(x_48, x_70, x_50);
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
x_79 = l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__1(x_49, x_76, x_3, x_4, x_5, x_6, x_7, x_78, x_46);
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
x_81 = l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__1(x_49, x_80, x_3, x_4, x_5, x_6, x_7, x_47, x_46);
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
x_93 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_90, x_91, x_3, x_4, x_5, x_6, x_7, x_92, x_10);
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
x_108 = l_Lake_inputBinFile___redArg___lam__1___closed__0;
x_109 = l_Substring_takeWhileAux___at___Lake_BuildMetadata_parse_spec__0(x_98, x_100, x_101);
x_110 = l_Substring_takeRightWhileAux___at___Lake_BuildMetadata_parse_spec__1(x_98, x_109, x_100);
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
x_118 = l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__1(x_99, x_115, x_3, x_4, x_5, x_6, x_7, x_117, x_96);
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
x_120 = l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__1(x_99, x_119, x_3, x_4, x_5, x_6, x_7, x_97, x_96);
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
x_25 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__0), 2, 1);
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
x_31 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__0), 2, 1);
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
lean_object* x_14; lean_object* x_15; 
x_14 = l___private_Lake_Build_Common_0__Lake_mkLinkOrder___redArg(x_1, x_12, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec_ref(x_11);
x_17 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec_ref(x_14);
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
lean_dec_ref(x_15);
x_22 = lean_ctor_get(x_18, 3);
x_23 = lean_ctor_get(x_18, 12);
lean_inc_ref(x_23);
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
lean_inc_ref(x_22);
x_30 = lean_array_push(x_29, x_22);
x_31 = l_Array_append___redArg(x_28, x_30);
lean_dec_ref(x_30);
x_32 = l_Lake_LeanInstall_ccLinkFlags(x_5, x_18);
lean_dec_ref(x_18);
x_33 = l_Array_append___redArg(x_31, x_32);
lean_dec_ref(x_32);
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
lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_62 = lean_ctor_get(x_19, 0);
x_63 = lean_ctor_get_uint8(x_19, sizeof(void*)*3);
x_64 = lean_ctor_get(x_19, 1);
x_65 = lean_ctor_get(x_19, 2);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_62);
lean_dec(x_19);
x_66 = l___private_Lake_Build_Common_0__Lake_mkLinkObjArgs(x_2, x_21);
lean_dec(x_21);
x_67 = l_Array_append___redArg(x_66, x_3);
x_68 = l_Array_append___redArg(x_67, x_4);
x_69 = l_Lake_buildLeanSharedLib___lam__0___closed__0;
lean_inc_ref(x_22);
x_70 = lean_array_push(x_69, x_22);
x_71 = l_Array_append___redArg(x_68, x_70);
lean_dec_ref(x_70);
x_72 = l_Lake_LeanInstall_ccLinkFlags(x_5, x_18);
lean_dec_ref(x_18);
x_73 = l_Array_append___redArg(x_71, x_72);
lean_dec_ref(x_72);
x_74 = l_Lake_compileExe(x_6, x_73, x_23, x_62, x_20);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
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
x_78 = lean_ctor_get(x_75, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_75, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_80 = x_75;
} else {
 lean_dec_ref(x_75);
 x_80 = lean_box(0);
}
x_81 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_64);
lean_ctor_set(x_81, 2, x_65);
lean_ctor_set_uint8(x_81, sizeof(void*)*3, x_63);
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_78);
lean_ctor_set(x_82, 1, x_81);
if (lean_is_scalar(x_77)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_77;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_76);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_84 = lean_ctor_get(x_74, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_85 = x_74;
} else {
 lean_dec_ref(x_74);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get(x_75, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_75, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_88 = x_75;
} else {
 lean_dec_ref(x_75);
 x_88 = lean_box(0);
}
x_89 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_64);
lean_ctor_set(x_89, 2, x_65);
lean_ctor_set_uint8(x_89, sizeof(void*)*3, x_63);
if (lean_is_scalar(x_88)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_88;
}
lean_ctor_set(x_90, 0, x_86);
lean_ctor_set(x_90, 1, x_89);
if (lean_is_scalar(x_85)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_85;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_84);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec_ref(x_11);
lean_dec_ref(x_6);
x_92 = !lean_is_exclusive(x_14);
if (x_92 == 0)
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_14, 0);
lean_dec(x_93);
x_94 = !lean_is_exclusive(x_15);
if (x_94 == 0)
{
return x_14;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_15, 0);
x_96 = lean_ctor_get(x_15, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_15);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_14, 0, x_97);
return x_14;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_98 = lean_ctor_get(x_14, 1);
lean_inc(x_98);
lean_dec(x_14);
x_99 = lean_ctor_get(x_15, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_15, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_101 = x_15;
} else {
 lean_dec_ref(x_15);
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
}
static lean_object* _init_l_Lake_buildLeanExe___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_System_FilePath_exeExtension;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; uint64_t x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
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
x_42 = l_Lake_platformTrace___closed__1;
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_array_get_size(x_3);
x_45 = lean_nat_dec_lt(x_43, x_44);
if (x_45 == 0)
{
lean_dec(x_44);
x_23 = x_42;
goto block_41;
}
else
{
uint8_t x_46; 
x_46 = lean_nat_dec_le(x_44, x_44);
if (x_46 == 0)
{
lean_dec(x_44);
x_23 = x_42;
goto block_41;
}
else
{
size_t x_47; size_t x_48; uint64_t x_49; 
x_47 = 0;
x_48 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_49 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_buildLeanO_spec__2(x_3, x_47, x_48, x_42);
x_23 = x_49;
goto block_41;
}
}
block_41:
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
x_40 = l_Lake_buildArtifactUnlessUpToDate(x_5, x_21, x_37, x_38, x_39, x_39, x_7, x_8, x_9, x_10, x_11, x_36, x_13);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; 
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
x_21 = l_Lake_Job_mapM___at___Lake_buildLeanO_spec__3___redArg(x_18, x_16, x_19, x_20, x_7, x_8, x_9, x_10, x_11, x_14, x_13);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_12);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_12);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
x_20 = l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg(x_17, x_15, x_18, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
x_13 = l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___redArg(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
x_14 = l_Lake_Job_bindM___at___Lake_buildLeanExe_spec__0(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_5);
x_15 = l_Lake_buildLeanExe___lam__0(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
x_15 = l_Lake_buildLeanExe___lam__1(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
x_15 = l_Lake_buildLeanExe___lam__2(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_6);
x_15 = l_Lake_buildLeanExe(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_2);
return x_15;
}
}
lean_object* initialize_Lean_Data_Json(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Job_Monad(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Monad(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_IO(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_JsonObject(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Target_Fetch(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Actions(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Common(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Json(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Job_Monad(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Monad(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_IO(builtin, lean_io_mk_world());
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
l_Prod_toJson___at___Array_toJson___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__0_spec__0___closed__0 = _init_l_Prod_toJson___at___Array_toJson___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__0_spec__0___closed__0();
lean_mark_persistent(l_Prod_toJson___at___Array_toJson___at___Lake_toJsonBuildMetadata____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59__spec__0_spec__0___closed__0);
l_Lake_toJsonBuildMetadata___closed__0____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_ = _init_l_Lake_toJsonBuildMetadata___closed__0____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_();
lean_mark_persistent(l_Lake_toJsonBuildMetadata___closed__0____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_);
l_Lake_toJsonBuildMetadata___closed__1____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_ = _init_l_Lake_toJsonBuildMetadata___closed__1____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_();
lean_mark_persistent(l_Lake_toJsonBuildMetadata___closed__1____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_);
l_Lake_toJsonBuildMetadata___closed__2____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_ = _init_l_Lake_toJsonBuildMetadata___closed__2____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_();
lean_mark_persistent(l_Lake_toJsonBuildMetadata___closed__2____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_);
l_Lake_toJsonBuildMetadata___closed__3____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_ = _init_l_Lake_toJsonBuildMetadata___closed__3____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_();
lean_mark_persistent(l_Lake_toJsonBuildMetadata___closed__3____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_);
l_Lake_toJsonBuildMetadata___closed__4____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_ = _init_l_Lake_toJsonBuildMetadata___closed__4____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_();
lean_mark_persistent(l_Lake_toJsonBuildMetadata___closed__4____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_);
l_Lake_toJsonBuildMetadata___closed__5____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_ = _init_l_Lake_toJsonBuildMetadata___closed__5____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_();
lean_mark_persistent(l_Lake_toJsonBuildMetadata___closed__5____x40_Lake_Build_Common_1618911186____hygCtx___hyg_59_);
l_Lake_instToJsonBuildMetadata___closed__0 = _init_l_Lake_instToJsonBuildMetadata___closed__0();
lean_mark_persistent(l_Lake_instToJsonBuildMetadata___closed__0);
l_Lake_instToJsonBuildMetadata = _init_l_Lake_instToJsonBuildMetadata();
lean_mark_persistent(l_Lake_instToJsonBuildMetadata);
l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__1___closed__0 = _init_l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__1___closed__0();
lean_mark_persistent(l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__1___closed__0);
l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__2_spec__2___closed__0 = _init_l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__2_spec__2___closed__0();
lean_mark_persistent(l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__2_spec__2___closed__0);
l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__2_spec__2___closed__1 = _init_l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__2_spec__2___closed__1();
lean_mark_persistent(l_Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__2_spec__2___closed__1);
l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__2___closed__0 = _init_l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__2___closed__0();
lean_mark_persistent(l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__2___closed__0);
l_Option_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5_spec__5___closed__0 = _init_l_Option_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5_spec__5___closed__0();
lean_mark_persistent(l_Option_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5_spec__5___closed__0);
l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5___closed__0 = _init_l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5___closed__0();
lean_mark_persistent(l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__5___closed__0);
l_Prod_fromJson_x3f___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__7_spec__7_spec__7___closed__0 = _init_l_Prod_fromJson_x3f___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__7_spec__7_spec__7___closed__0();
lean_mark_persistent(l_Prod_fromJson_x3f___at___Array_fromJson_x3f___at___Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__7_spec__7_spec__7___closed__0);
l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__7___closed__0 = _init_l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__7___closed__0();
lean_mark_persistent(l_Option_fromJson_x3f___at___Lake_BuildMetadata_fromJson_x3f_spec__7___closed__0);
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
l_Lake_BuildMetadata_fromJson_x3f___closed__8 = _init_l_Lake_BuildMetadata_fromJson_x3f___closed__8();
lean_mark_persistent(l_Lake_BuildMetadata_fromJson_x3f___closed__8);
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
lean_mark_persistent(l_Lake_buildAction___redArg___closed__0);
l_Lake_buildAction___redArg___closed__1 = _init_l_Lake_buildAction___redArg___closed__1();
lean_mark_persistent(l_Lake_buildAction___redArg___closed__1);
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
l_Array_filterMapM___at___Lake_inputDir_spec__0___closed__0 = _init_l_Array_filterMapM___at___Lake_inputDir_spec__0___closed__0();
lean_mark_persistent(l_Array_filterMapM___at___Lake_inputDir_spec__0___closed__0);
l_Lake_inputDir___lam__2___closed__0 = _init_l_Lake_inputDir___lam__2___closed__0();
lean_mark_persistent(l_Lake_inputDir___lam__2___closed__0);
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

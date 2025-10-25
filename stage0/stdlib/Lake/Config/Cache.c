// Lean compiler output
// Module: Lake.Config.Cache
// Imports: public import Lake.Util.Log public import Lake.Config.Artifact import Lake.Config.InstallPath import Lake.Build.Actions import Lake.Util.Url import Lake.Util.Proc import Lake.Util.Reservoir import Lake.Util.IO
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
LEAN_EXPORT lean_object* l_Lake_CacheService_withRepoScope___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_insertCore___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_revisionPath___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifactPaths___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_System_instInhabitedFilePath_default;
LEAN_EXPORT lean_object* l_Lake_Cache_ctorIdx(lean_object*);
lean_object* lean_io_prim_handle_lock(lean_object*, uint8_t);
static lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__3;
lean_object* l_Lean_Json_compress(lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__3;
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadService(lean_object*, lean_object*, lean_object*);
static uint8_t l_Lake_CacheService_downloadArtifact___closed__6;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__0;
lean_object* l_Lean_JsonNumber_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_CacheService_artifactUrl___closed__0;
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_withRepoScope(lean_object*, uint8_t);
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_collectOutputDescrs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_artifactContentType;
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___redArg(uint64_t, lean_object*);
lean_object* lean_io_remove_file(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, uint8_t, lean_object*);
static lean_object* l_Lake_CacheService_downloadArtifacts___closed__0;
static lean_object* l_Lake_Cache_getArtifact_x3f___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_CacheService_revisionUrl___closed__1;
static lean_object* l_Lake_Cache_readOutputs_x3f___closed__1;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_outputsFile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadOutputArtifacts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
static lean_object* l_Lake_Cache_readOutputs_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lake_CacheRef_mk___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__13;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Prod_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__8___closed__0;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__4;
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___elam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__2___redArg(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_instInhabitedCache_default;
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__15;
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_metadata(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_outputsFile(lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Lake_Cache_artifactDir(lean_object*);
lean_object* l_Lake_download(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputsCore(lean_object*, lean_object*, uint64_t, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_CacheService_downloadArtifact___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Reservoir_lakeHeaders;
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadOutputArtifacts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_artifactUrl(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_CacheService_revisionUrl___closed__0;
static lean_object* l_Lake_CacheService_downloadArtifact___closed__4;
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact(lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__8;
LEAN_EXPORT lean_object* l_Lake_CacheMap_insertCore(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Cache_revisionDir___closed__0;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lake_CacheMap_parse___closed__0;
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5;
uint8_t l_System_FilePath_pathExists(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_mapContentType;
lean_object* l_Lake_Hash_hex(uint64_t);
static lean_object* l_Lake_CacheMap_updateFile___closed__1;
LEAN_EXPORT lean_object* l_Lake_CacheService_ctorIdx___boxed(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Cache_outputsFile___closed__0;
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_outputsDir(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_updateFile_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_CacheService_mapContentType___closed__0;
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifactPaths(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12;
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadRevisionOutputs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__7;
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
static lean_object* l_Lake_CacheService_artifactUrl___closed__1;
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__2(lean_object*, uint64_t, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheRef_get_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__0;
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedCache;
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_updateFile_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_CacheService_downloadArtifact___closed__2;
lean_object* lean_st_ref_take(lean_object*);
static lean_object* l_Lake_CacheService_downloadArtifact___closed__0;
lean_object* l_Lake_createParentDirs(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0(lean_object*, uint64_t, lean_object*);
static lean_object* l_Lake_CacheMap_parse___closed__1;
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__2;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_IO_FS_Handle_putStrLn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact___at___00Lake_CacheService_uploadArtifacts___elam__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Lake_CacheMap_schemaVersion___closed__0;
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_writeFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_artifactUrl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_get_x3f___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__3;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_updateFile_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_updateFile(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_CacheMap_collectOutputDescrs___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_updateFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_writeFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_reservoirService(lean_object*, uint8_t);
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__0;
static lean_object* l_Lake_CacheService_downloadArtifact___closed__1;
static lean_object* l_Lake_Cache_outputsDir___closed__0;
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifactPaths___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Hash_instHashable___lam__0___boxed(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_schemaVersion;
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_get_x3f(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_readOutputs_x3f(lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_revisionUrl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_revisionDir(lean_object*);
lean_object* l_String_posOfAux(lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputsCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Cache_artifactDir___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lake_ArtifactDescr_ofFilePath_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__1;
LEAN_EXPORT lean_object* l_String_splitAux___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_revisionUrl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16;
LEAN_EXPORT lean_object* l_Lake_Cache_writeMap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Cache_revisionPath___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_artifactPath___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_CacheMap_parse___closed__4;
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact___at___00Lake_CacheService_uploadArtifacts___elam__0_spec__0(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lake_CacheService_uploadArtifact___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_CacheMap_load___closed__0;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__1;
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact___at___00Lake_CacheService_downloadArtifacts___elam__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Cache_revisionPath(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_CacheService_reservoirService___closed__0;
LEAN_EXPORT lean_object* l_Lake_Cache_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3_spec__3_spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__1;
static lean_object* l_Lake_CacheService_artifactUrl___closed__2;
static lean_object* l_Lake_CacheService_uploadRevisionOutputs___closed__0;
lean_object* lean_io_prim_handle_get_line(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Hash_ofJsonNumber_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheRef_mk(lean_object*);
lean_object* l_IO_FS_readFile(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Prod_toJson___at___00Lake_CacheMap_updateFile_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadService(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__14;
static lean_object* l_Lake_CacheMap_writeFile___closed__1;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0(lean_object*, lean_object*, uint64_t);
static lean_object* l_Lake_CacheMap_parse___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lake_CacheMap_parse___closed__2;
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11;
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact___at___00Lake_CacheService_downloadArtifacts___elam__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_CacheMap_updateFile___closed__0;
static lean_object* l_Lake_Cache_getArtifactPaths___closed__0;
LEAN_EXPORT lean_object* l_String_splitAux___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifactPaths___lam__0(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4;
static lean_object* l_Lake_instInhabitedCache_default___closed__0;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
static lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__2;
static lean_object* l_Lake_Cache_artifactPath___closed__0;
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtsService(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_CacheMap_writeFile___closed__0;
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_toJson___at___00Lake_CacheMap_updateFile_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__6___redArg(uint64_t, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Lake_uriEncode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(uint64_t, lean_object*, lean_object*);
static lean_object* l_Lake_CacheMap_parse___closed__5;
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_collectOutputDescrs_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2(lean_object*, lean_object*, uint64_t, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__2;
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadRevisionOutputs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact(uint64_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0;
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___redArg(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_writeMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_readOutputs_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_load(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_reservoirService___boxed(lean_object*, lean_object*);
static size_t l_Lake_CacheService_downloadArtifact___closed__7;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3_spec__3_spec__3___redArg(lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
static lean_object* l_Lake_Cache_getArtifact___closed__0;
size_t lean_usize_sub(size_t, size_t);
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_updateFile_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___redArg(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___redArg(lean_object*, lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_load_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_updateFile_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__2;
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lake_Cache_getArtifact_x3f___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
static uint8_t l_Lake_CacheService_downloadArtifact___closed__5;
lean_object* lean_st_ref_set(lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__1;
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs(lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_load_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_collectOutputDescrs___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_computeBinFileHash(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheRef_get_x3f(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_artifactPath(lean_object*, uint64_t, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lake_instDecidableEqHash___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__6(lean_object*, uint64_t, lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6;
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_io_prim_handle_rewind(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Hash_fromJson_x3f(lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9;
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__1;
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_load___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_CacheService_revisionUrl___closed__2;
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___redArg(lean_object*, uint64_t, lean_object*, lean_object*);
lean_object* l_Lake_getUrl_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_collectOutputDescrs(lean_object*, lean_object*);
static lean_object* l_Prod_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__8___closed__1;
static lean_object* l_Lake_CacheService_artifactContentType___closed__0;
static lean_object* _init_l_Lake_CacheMap_schemaVersion___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("2025-09-10", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_CacheMap_schemaVersion() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_CacheMap_schemaVersion___closed__0;
return x_1;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": invalid schema version on line 1: ", 36, 36);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": unknown schema version '", 26, 26);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'; may not parse correctly", 26, 26);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": expected schema version on line 1", 35, 35);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_string_utf8_byte_size(x_2);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_15, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = l_Lean_Json_parse(x_2);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_5 = x_19;
goto block_14;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = l_Lean_Json_getStr_x3f(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_5 = x_22;
goto block_14;
}
else
{
lean_object* x_23; lean_object* x_35; uint8_t x_36; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec_ref(x_21);
x_35 = l_Lake_CacheMap_schemaVersion___closed__0;
x_36 = lean_string_dec_eq(x_23, x_35);
if (x_36 == 0)
{
goto block_34;
}
else
{
if (x_17 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_23);
lean_dec_ref(x_1);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_3);
return x_38;
}
else
{
goto block_34;
}
}
block_34:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__1;
x_25 = lean_string_append(x_1, x_24);
x_26 = lean_string_append(x_25, x_23);
lean_dec(x_23);
x_27 = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__2;
x_28 = lean_string_append(x_26, x_27);
x_29 = 2;
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_29);
x_31 = lean_box(0);
x_32 = lean_array_push(x_3, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_2);
x_39 = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__3;
x_40 = lean_string_append(x_1, x_39);
x_41 = 3;
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
x_43 = lean_array_get_size(x_3);
x_44 = lean_array_push(x_3, x_42);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
block_14:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__0;
x_7 = lean_string_append(x_1, x_6);
x_8 = lean_string_append(x_7, x_5);
lean_dec_ref(x_5);
x_9 = 2;
x_10 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_9);
x_11 = lean_box(0);
x_12 = lean_array_push(x_3, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__2___redArg(uint64_t x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; uint64_t x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_unbox_uint64(x_4);
x_7 = lean_uint64_dec_eq(x_6, x_1);
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
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__2(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = 32;
x_8 = lean_unbox_uint64(x_4);
x_9 = lean_uint64_shift_right(x_8, x_7);
x_10 = lean_unbox_uint64(x_4);
x_11 = lean_uint64_xor(x_10, x_9);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_6);
lean_dec(x_6);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; size_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get(x_2, 2);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_2);
x_26 = lean_array_get_size(x_1);
x_27 = 32;
x_28 = lean_unbox_uint64(x_23);
x_29 = lean_uint64_shift_right(x_28, x_27);
x_30 = lean_unbox_uint64(x_23);
x_31 = lean_uint64_xor(x_30, x_29);
x_32 = 16;
x_33 = lean_uint64_shift_right(x_31, x_32);
x_34 = lean_uint64_xor(x_31, x_33);
x_35 = lean_uint64_to_usize(x_34);
x_36 = lean_usize_of_nat(x_26);
lean_dec(x_26);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3_spec__3_spec__3___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3_spec__3_spec__3___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3_spec__3___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3___redArg(lean_object* x_1) {
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
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3_spec__3___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__6___redArg(uint64_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_unbox_uint64(x_5);
x_9 = lean_uint64_dec_eq(x_8, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__6___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
x_11 = lean_box_uint64(x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_15 = lean_unbox_uint64(x_12);
x_16 = lean_uint64_dec_eq(x_15, x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__6___redArg(x_1, x_2, x_14);
x_18 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_12);
x_19 = lean_box_uint64(x_1);
x_20 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_2);
lean_ctor_set(x_20, 2, x_14);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__6(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__6___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___redArg(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; uint8_t x_20; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_2, x_8);
x_10 = lean_uint64_xor(x_2, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_6, x_18);
x_20 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__2___redArg(x_2, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_5, x_21);
lean_dec(x_5);
x_23 = lean_box_uint64(x_2);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 2, x_19);
x_25 = lean_array_uset(x_6, x_18, x_24);
x_26 = lean_unsigned_to_nat(4u);
x_27 = lean_nat_mul(x_22, x_26);
x_28 = lean_unsigned_to_nat(3u);
x_29 = lean_nat_div(x_27, x_28);
lean_dec(x_27);
x_30 = lean_array_get_size(x_25);
x_31 = lean_nat_dec_le(x_29, x_30);
lean_dec(x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3___redArg(x_25);
lean_ctor_set(x_1, 1, x_32);
lean_ctor_set(x_1, 0, x_22);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_25);
lean_ctor_set(x_1, 0, x_22);
return x_1;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_box(0);
x_34 = lean_array_uset(x_6, x_18, x_33);
x_35 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__6___redArg(x_2, x_3, x_19);
x_36 = lean_array_uset(x_34, x_18, x_35);
lean_ctor_set(x_1, 1, x_36);
return x_1;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; size_t x_46; size_t x_47; size_t x_48; size_t x_49; size_t x_50; lean_object* x_51; uint8_t x_52; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_1);
x_39 = lean_array_get_size(x_38);
x_40 = 32;
x_41 = lean_uint64_shift_right(x_2, x_40);
x_42 = lean_uint64_xor(x_2, x_41);
x_43 = 16;
x_44 = lean_uint64_shift_right(x_42, x_43);
x_45 = lean_uint64_xor(x_42, x_44);
x_46 = lean_uint64_to_usize(x_45);
x_47 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_48 = 1;
x_49 = lean_usize_sub(x_47, x_48);
x_50 = lean_usize_land(x_46, x_49);
x_51 = lean_array_uget(x_38, x_50);
x_52 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__2___redArg(x_2, x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_37, x_53);
lean_dec(x_37);
x_55 = lean_box_uint64(x_2);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_3);
lean_ctor_set(x_56, 2, x_51);
x_57 = lean_array_uset(x_38, x_50, x_56);
x_58 = lean_unsigned_to_nat(4u);
x_59 = lean_nat_mul(x_54, x_58);
x_60 = lean_unsigned_to_nat(3u);
x_61 = lean_nat_div(x_59, x_60);
lean_dec(x_59);
x_62 = lean_array_get_size(x_57);
x_63 = lean_nat_dec_le(x_61, x_62);
lean_dec(x_62);
lean_dec(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3___redArg(x_57);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_54);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_54);
lean_ctor_set(x_66, 1, x_57);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_box(0);
x_68 = lean_array_uset(x_38, x_50, x_67);
x_69 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__6___redArg(x_2, x_3, x_51);
x_70 = lean_array_uset(x_68, x_50, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_37);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Prod_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__8___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected pair, got '", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Prod_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__8(lean_object* x_1) {
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
x_17 = l_Lake_Hash_fromJson_x3f(x_16);
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
x_3 = l_Prod_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__8___closed__0;
x_4 = lean_unsigned_to_nat(80u);
x_5 = l_Lean_Json_pretty(x_2, x_4);
x_6 = lean_string_append(x_3, x_5);
lean_dec_ref(x_5);
x_7 = l_Prod_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__8___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": invalid JSON on line ", 23, 23);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint32_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_20; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_9 = 10;
lean_inc(x_7);
x_10 = l_String_posOfAux(x_3, x_9, x_6, x_7);
x_33 = lean_string_utf8_extract(x_3, x_7, x_10);
lean_dec(x_7);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_string_utf8_byte_size(x_33);
x_36 = l_Substring_takeWhileAux___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__0(x_33, x_35, x_34);
x_37 = l_Substring_takeRightWhileAux___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__1(x_33, x_36, x_35);
x_38 = lean_string_utf8_extract(x_33, x_36, x_37);
lean_dec(x_37);
lean_dec(x_36);
x_39 = lean_string_utf8_byte_size(x_38);
lean_dec_ref(x_38);
x_40 = lean_nat_dec_eq(x_39, x_34);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = l_Lean_Json_parse(x_33);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
x_20 = x_42;
goto block_32;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec_ref(x_41);
x_44 = l_Prod_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__8(x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
x_20 = x_45;
goto block_32;
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint64_t x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_44, 0);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_unbox_uint64(x_48);
lean_dec(x_48);
x_51 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___redArg(x_5, x_50, x_49);
lean_inc_ref(x_51);
lean_ctor_set_tag(x_44, 0);
lean_ctor_set(x_44, 0, x_51);
x_11 = x_44;
x_12 = x_51;
x_13 = lean_box(0);
goto block_19;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint64_t x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_44, 0);
lean_inc(x_52);
lean_dec(x_44);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_unbox_uint64(x_53);
lean_dec(x_53);
x_56 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___redArg(x_5, x_55, x_54);
lean_inc_ref(x_56);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_11 = x_57;
x_12 = x_56;
x_13 = lean_box(0);
goto block_19;
}
}
}
}
else
{
lean_object* x_58; 
lean_dec_ref(x_33);
lean_dec(x_10);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_5);
return x_58;
}
block_19:
{
uint8_t x_14; 
x_14 = lean_string_utf8_at_end(x_3, x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_11);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_4, x_15);
lean_dec(x_4);
x_17 = lean_string_utf8_next_fast(x_3, x_10);
lean_dec(x_10);
x_4 = x_16;
x_5 = x_12;
x_7 = x_17;
goto _start;
}
else
{
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_11;
}
}
block_32:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__0;
lean_inc_ref(x_2);
x_22 = lean_string_append(x_2, x_21);
lean_inc(x_4);
x_23 = l_Nat_reprFast(x_4);
x_24 = lean_string_append(x_22, x_23);
lean_dec_ref(x_23);
x_25 = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__1;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_string_append(x_26, x_20);
lean_dec_ref(x_20);
x_28 = 2;
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
lean_inc_ref(x_1);
x_30 = lean_apply_2(x_1, x_29, lean_box(0));
lean_inc_ref(x_5);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_5);
x_11 = x_31;
x_12 = x_5;
x_13 = lean_box(0);
goto block_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint32_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_20; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_9 = 10;
lean_inc(x_6);
x_10 = l_String_posOfAux(x_2, x_9, x_5, x_6);
x_33 = lean_string_utf8_extract(x_2, x_6, x_10);
lean_dec(x_6);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_string_utf8_byte_size(x_33);
x_36 = l_Substring_takeWhileAux___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__0(x_33, x_35, x_34);
x_37 = l_Substring_takeRightWhileAux___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__1(x_33, x_36, x_35);
x_38 = lean_string_utf8_extract(x_33, x_36, x_37);
lean_dec(x_37);
lean_dec(x_36);
x_39 = lean_string_utf8_byte_size(x_38);
lean_dec_ref(x_38);
x_40 = lean_nat_dec_eq(x_39, x_34);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = l_Lean_Json_parse(x_33);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
x_20 = x_42;
goto block_32;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec_ref(x_41);
x_44 = l_Prod_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__8(x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
x_20 = x_45;
goto block_32;
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint64_t x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_44, 0);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_unbox_uint64(x_48);
lean_dec(x_48);
x_51 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___redArg(x_4, x_50, x_49);
lean_inc_ref(x_51);
lean_ctor_set_tag(x_44, 0);
lean_ctor_set(x_44, 0, x_51);
x_11 = x_44;
x_12 = x_51;
x_13 = lean_box(0);
goto block_19;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint64_t x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_44, 0);
lean_inc(x_52);
lean_dec(x_44);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_unbox_uint64(x_53);
lean_dec(x_53);
x_56 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___redArg(x_4, x_55, x_54);
lean_inc_ref(x_56);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_11 = x_57;
x_12 = x_56;
x_13 = lean_box(0);
goto block_19;
}
}
}
}
else
{
lean_object* x_58; 
lean_dec_ref(x_33);
lean_dec(x_10);
lean_dec_ref(x_7);
lean_dec(x_3);
lean_dec_ref(x_1);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_4);
return x_58;
}
block_19:
{
uint8_t x_14; 
x_14 = lean_string_utf8_at_end(x_2, x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_11);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_3, x_15);
lean_dec(x_3);
x_17 = lean_string_utf8_next_fast(x_2, x_10);
lean_dec(x_10);
x_18 = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0(x_7, x_1, x_2, x_16, x_12, x_5, x_17);
return x_18;
}
else
{
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec_ref(x_7);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_11;
}
}
block_32:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__0;
lean_inc_ref(x_1);
x_22 = lean_string_append(x_1, x_21);
lean_inc(x_3);
x_23 = l_Nat_reprFast(x_3);
x_24 = lean_string_append(x_22, x_23);
lean_dec_ref(x_23);
x_25 = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__1;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_string_append(x_26, x_20);
lean_dec_ref(x_20);
x_28 = 2;
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
lean_inc_ref(x_7);
x_30 = lean_apply_2(x_7, x_29, lean_box(0));
lean_inc_ref(x_4);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_4);
x_11 = x_31;
x_12 = x_4;
x_13 = lean_box(0);
goto block_19;
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeWhileAux___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeRightWhileAux___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__2___redArg(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__2(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__6___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_6 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__6(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___redArg(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_6 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_2(x_2, x_1, lean_box(0));
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CacheMap_parse___elam__0___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_2(x_1, x_2, lean_box(0));
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CacheMap_parse___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0_spec__0___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_8 = lean_array_uget(x_1, x_2);
lean_inc_ref(x_5);
x_9 = l_Lake_CacheMap_parse___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0_spec__0___redArg(x_5, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_10;
goto _start;
}
else
{
lean_object* x_14; 
lean_dec_ref(x_5);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_4);
return x_14;
}
}
}
static lean_object* _init_l_Lake_CacheMap_parse___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_CacheMap_parse___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lake_CacheMap_parse___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_CacheMap_parse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_CacheMap_parse___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_CacheMap_parse___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_CacheMap_parse___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_CacheMap_parse___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_CacheMap_parse___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_CacheMap_parse___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint32_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_9 = 10;
x_10 = lean_string_utf8_byte_size(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_String_posOfAux(x_2, x_9, x_10, x_11);
x_22 = lean_string_utf8_extract(x_2, x_11, x_12);
x_23 = lean_string_utf8_byte_size(x_22);
x_24 = l_Substring_takeWhileAux___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__0(x_22, x_23, x_11);
x_25 = l_Substring_takeRightWhileAux___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__1(x_22, x_24, x_23);
x_26 = lean_string_utf8_extract(x_22, x_24, x_25);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_22);
x_27 = l_Lake_CacheMap_parse___closed__5;
lean_inc_ref(x_1);
x_28 = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(x_1, x_26, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_array_get_size(x_29);
x_31 = lean_nat_dec_lt(x_11, x_30);
if (x_31 == 0)
{
lean_dec(x_30);
lean_dec(x_29);
x_13 = lean_box(0);
goto block_21;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_30, x_30);
if (x_32 == 0)
{
lean_dec(x_30);
lean_dec(x_29);
x_13 = lean_box(0);
goto block_21;
}
else
{
lean_object* x_33; size_t x_34; size_t x_35; lean_object* x_36; 
x_33 = lean_box(0);
x_34 = 0;
x_35 = lean_usize_of_nat(x_30);
lean_dec(x_30);
lean_inc_ref(x_3);
x_36 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(x_29, x_34, x_35, x_33, x_3);
lean_dec(x_29);
lean_dec_ref(x_36);
x_13 = lean_box(0);
goto block_21;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_1);
x_37 = lean_ctor_get(x_28, 1);
lean_inc(x_37);
lean_dec_ref(x_28);
x_38 = lean_array_get_size(x_37);
x_39 = lean_nat_dec_lt(x_11, x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec_ref(x_3);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
else
{
uint8_t x_42; 
x_42 = lean_nat_dec_le(x_38, x_38);
if (x_42 == 0)
{
lean_dec(x_38);
lean_dec(x_37);
lean_dec_ref(x_3);
x_5 = lean_box(0);
goto block_8;
}
else
{
lean_object* x_43; size_t x_44; size_t x_45; lean_object* x_46; 
x_43 = lean_box(0);
x_44 = 0;
x_45 = lean_usize_of_nat(x_38);
lean_dec(x_38);
x_46 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(x_37, x_44, x_45, x_43, x_3);
lean_dec(x_37);
lean_dec_ref(x_46);
x_5 = lean_box(0);
goto block_8;
}
}
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
block_21:
{
uint8_t x_14; 
x_14 = lean_string_utf8_at_end(x_2, x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(2u);
x_16 = l_Lake_CacheMap_parse___closed__4;
x_17 = lean_string_utf8_next_fast(x_2, x_12);
lean_dec(x_12);
x_18 = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0(x_3, x_1, x_2, x_15, x_16, x_10, x_17);
lean_dec(x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_19 = l_Lake_CacheMap_parse___closed__4;
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_CacheMap_parse___elam__0___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CacheMap_parse___elam__0(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_CacheMap_parse___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0_spec__0___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CacheMap_parse___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0_spec__0(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(x_1, x_7, x_8, x_4, x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CacheMap_parse(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_io_prim_handle_get_line(x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_24 = lean_string_utf8_byte_size(x_8);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_eq(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = l_Lean_Json_parse(x_8);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_9 = x_28;
goto block_23;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec_ref(x_27);
x_30 = l_Prod_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__8(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_9 = x_31;
goto block_23;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint64_t x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_3, x_35);
lean_dec(x_3);
x_37 = lean_unbox_uint64(x_33);
lean_dec(x_33);
x_38 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___redArg(x_4, x_37, x_34);
x_3 = x_36;
x_4 = x_38;
goto _start;
}
}
}
else
{
lean_object* x_40; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec_ref(x_2);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_4);
lean_ctor_set(x_40, 1, x_5);
return x_40;
}
block_23:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_10 = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__0;
lean_inc_ref(x_2);
x_11 = lean_string_append(x_2, x_10);
lean_inc(x_3);
x_12 = l_Nat_reprFast(x_3);
x_13 = lean_string_append(x_11, x_12);
lean_dec_ref(x_12);
x_14 = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__1;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_string_append(x_15, x_9);
lean_dec_ref(x_9);
x_17 = 2;
x_18 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_17);
x_19 = lean_array_push(x_5, x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_3, x_20);
lean_dec(x_3);
x_3 = x_21;
x_5 = x_19;
goto _start;
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_41 = lean_ctor_get(x_7, 0);
lean_inc(x_41);
lean_dec_ref(x_7);
x_42 = lean_io_error_to_string(x_41);
x_43 = 3;
x_44 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_43);
x_45 = lean_array_get_size(x_5);
x_46 = lean_array_push(x_5, x_44);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_prim_handle_get_line(x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
lean_inc_ref(x_2);
x_7 = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(x_2, x_6, x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_unsigned_to_nat(2u);
x_10 = l_Lake_CacheMap_parse___closed__4;
x_11 = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(x_1, x_2, x_9, x_10, x_8);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec_ref(x_2);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_2);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec_ref(x_5);
x_17 = lean_io_error_to_string(x_16);
x_18 = 3;
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
x_20 = lean_array_get_size(x_3);
x_21 = lean_array_push(x_3, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore(x_1, x_2, x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lake_CacheMap_load___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": failed to open file: ", 23, 23);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_load(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = 0;
x_5 = lean_io_prim_handle_mk(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = 0;
x_8 = lean_io_prim_handle_lock(x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec_ref(x_8);
x_9 = lean_io_prim_handle_get_line(x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
lean_inc_ref(x_1);
x_11 = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(x_1, x_10, x_2);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lake_CacheMap_parse___closed__4;
x_15 = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(x_6, x_1, x_13, x_14, x_12);
lean_dec(x_6);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_6);
lean_dec_ref(x_1);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_6);
lean_dec_ref(x_1);
x_20 = lean_ctor_get(x_9, 0);
lean_inc(x_20);
lean_dec_ref(x_9);
x_21 = lean_io_error_to_string(x_20);
x_22 = 3;
x_23 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_22);
x_24 = lean_array_get_size(x_2);
x_25 = lean_array_push(x_2, x_23);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_6);
lean_dec_ref(x_1);
x_27 = lean_ctor_get(x_8, 0);
lean_inc(x_27);
lean_dec_ref(x_8);
x_28 = lean_io_error_to_string(x_27);
x_29 = 3;
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_29);
x_31 = lean_array_get_size(x_2);
x_32 = lean_array_push(x_2, x_30);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_34 = lean_ctor_get(x_5, 0);
lean_inc(x_34);
lean_dec_ref(x_5);
x_35 = l_Lake_CacheMap_load___closed__0;
x_36 = lean_string_append(x_1, x_35);
x_37 = lean_io_error_to_string(x_34);
x_38 = lean_string_append(x_36, x_37);
lean_dec_ref(x_37);
x_39 = 3;
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_39);
x_41 = lean_array_get_size(x_2);
x_42 = lean_array_push(x_2, x_40);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_load___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_CacheMap_load(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_load_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_9; lean_object* x_10; 
x_9 = 0;
x_10 = lean_io_prim_handle_mk(x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = 0;
x_13 = lean_io_prim_handle_lock(x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec_ref(x_13);
x_14 = lean_io_prim_handle_get_line(x_11);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_1);
x_17 = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(x_1, x_16, x_2);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_unsigned_to_nat(2u);
x_20 = l_Lake_CacheMap_parse___closed__4;
x_21 = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(x_11, x_1, x_19, x_20, x_18);
lean_dec(x_11);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_23);
lean_ctor_set(x_21, 0, x_14);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_free_object(x_14);
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_dec_ref(x_21);
x_4 = x_27;
x_5 = x_28;
x_6 = lean_box(0);
goto block_8;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_free_object(x_14);
lean_dec(x_11);
lean_dec_ref(x_1);
x_29 = lean_ctor_get(x_17, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
lean_dec_ref(x_17);
x_4 = x_29;
x_5 = x_30;
x_6 = lean_box(0);
goto block_8;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_14, 0);
lean_inc(x_31);
lean_dec(x_14);
lean_inc_ref(x_1);
x_32 = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(x_1, x_31, x_2);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = lean_unsigned_to_nat(2u);
x_35 = l_Lake_CacheMap_parse___closed__4;
x_36 = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(x_11, x_1, x_34, x_35, x_33);
lean_dec(x_11);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_37);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_dec_ref(x_36);
x_4 = x_42;
x_5 = x_43;
x_6 = lean_box(0);
goto block_8;
}
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_11);
lean_dec_ref(x_1);
x_44 = lean_ctor_get(x_32, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_32, 1);
lean_inc(x_45);
lean_dec_ref(x_32);
x_4 = x_44;
x_5 = x_45;
x_6 = lean_box(0);
goto block_8;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_11);
lean_dec_ref(x_1);
x_46 = lean_ctor_get(x_14, 0);
lean_inc(x_46);
lean_dec_ref(x_14);
x_47 = lean_io_error_to_string(x_46);
x_48 = 3;
x_49 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_48);
x_50 = lean_array_get_size(x_2);
x_51 = lean_array_push(x_2, x_49);
x_4 = x_50;
x_5 = x_51;
x_6 = lean_box(0);
goto block_8;
}
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_11);
lean_dec_ref(x_1);
x_52 = lean_ctor_get(x_13, 0);
lean_inc(x_52);
lean_dec_ref(x_13);
x_53 = lean_io_error_to_string(x_52);
x_54 = 3;
x_55 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_54);
x_56 = lean_array_get_size(x_2);
x_57 = lean_array_push(x_2, x_55);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_10, 0);
lean_inc(x_59);
lean_dec_ref(x_10);
if (lean_obj_tag(x_59) == 11)
{
lean_object* x_60; lean_object* x_61; 
lean_dec_ref(x_59);
lean_dec_ref(x_1);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_2);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_62 = l_Lake_CacheMap_load___closed__0;
x_63 = lean_string_append(x_1, x_62);
x_64 = lean_io_error_to_string(x_59);
x_65 = lean_string_append(x_63, x_64);
lean_dec_ref(x_64);
x_66 = 3;
x_67 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_66);
x_68 = lean_array_get_size(x_2);
x_69 = lean_array_push(x_2, x_67);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
block_8:
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_load_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_CacheMap_load_x3f(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Prod_toJson___at___00Lake_CacheMap_updateFile_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Prod_toJson___at___00Lake_CacheMap_updateFile_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint64_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Lake_Hash_hex(x_4);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l_Prod_toJson___at___00Lake_CacheMap_updateFile_spec__0___closed__0;
x_8 = lean_array_push(x_7, x_6);
x_9 = lean_array_push(x_8, x_3);
x_10 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_updateFile_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_ctor_get(x_3, 2);
lean_inc(x_8);
lean_inc(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Prod_toJson___at___00Lake_CacheMap_updateFile_spec__0(x_10);
x_12 = l_Lean_Json_compress(x_11);
x_13 = l_IO_FS_Handle_putStrLn(x_1, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_2 = x_14;
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec_ref(x_13);
x_17 = lean_io_error_to_string(x_16);
x_18 = 3;
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
x_20 = lean_array_get_size(x_4);
x_21 = lean_array_push(x_4, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_3, x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_array_uget(x_2, x_3);
x_10 = lean_box(0);
x_11 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_updateFile_spec__1(x_1, x_10, x_9, x_6);
lean_dec(x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
x_5 = x_12;
x_6 = x_13;
goto _start;
}
else
{
return x_11;
}
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_updateFile_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint64_t x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_7 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___redArg(x_1, x_6, x_4);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_updateFile_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_updateFile_spec__3___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_8 = lean_array_uget(x_3, x_4);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_updateFile_spec__3___redArg(x_6, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_4, x_10);
x_4 = x_11;
x_6 = x_9;
goto _start;
}
else
{
return x_6;
}
}
}
static lean_object* _init_l_Lake_CacheMap_updateFile___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Hash_instHashable___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_CacheMap_updateFile___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lake_instDecidableEqHash___boxed), 2, 0);
x_2 = l_instBEqOfDecidableEq___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_updateFile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_10; 
x_10 = l_Lake_createParentDirs(x_1);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; lean_object* x_12; 
lean_dec_ref(x_10);
x_11 = 4;
x_12 = lean_io_prim_handle_mk(x_1, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; lean_object* x_14; 
lean_dec_ref(x_12);
x_13 = 3;
x_14 = lean_io_prim_handle_mk(x_1, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = 1;
x_17 = lean_io_prim_handle_lock(x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec_ref(x_17);
x_18 = lean_io_prim_handle_get_line(x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
lean_inc_ref(x_1);
x_20 = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(x_1, x_19, x_3);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_unsigned_to_nat(2u);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lake_CacheMap_parse___closed__4;
x_25 = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(x_15, x_1, x_22, x_24, x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
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
x_49 = lean_ctor_get(x_2, 1);
x_50 = lean_array_get_size(x_49);
x_51 = lean_nat_dec_lt(x_23, x_50);
if (x_51 == 0)
{
lean_dec(x_50);
x_29 = x_26;
goto block_48;
}
else
{
uint8_t x_52; 
x_52 = lean_nat_dec_le(x_50, x_50);
if (x_52 == 0)
{
lean_dec(x_50);
x_29 = x_26;
goto block_48;
}
else
{
lean_object* x_53; lean_object* x_54; size_t x_55; size_t x_56; lean_object* x_57; 
x_53 = l_Lake_CacheMap_updateFile___closed__0;
x_54 = l_Lake_CacheMap_updateFile___closed__1;
x_55 = 0;
x_56 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_57 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__4(x_54, x_53, x_49, x_55, x_56, x_26);
x_29 = x_57;
goto block_48;
}
}
block_48:
{
lean_object* x_30; 
x_30 = lean_io_prim_handle_rewind(x_15);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec_ref(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc_ref(x_31);
lean_dec_ref(x_29);
x_32 = lean_array_get_size(x_31);
x_33 = lean_box(0);
x_34 = lean_nat_dec_lt(x_23, x_32);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_15);
if (lean_is_scalar(x_28)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_28;
}
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_27);
return x_35;
}
else
{
uint8_t x_36; 
x_36 = lean_nat_dec_le(x_32, x_32);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_15);
if (lean_is_scalar(x_28)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_28;
}
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_27);
return x_37;
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; 
lean_dec(x_28);
x_38 = 0;
x_39 = lean_usize_of_nat(x_32);
lean_dec(x_32);
x_40 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__2(x_15, x_31, x_38, x_39, x_33, x_27);
lean_dec_ref(x_31);
lean_dec(x_15);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec_ref(x_29);
lean_dec(x_15);
x_41 = lean_ctor_get(x_30, 0);
lean_inc(x_41);
lean_dec_ref(x_30);
x_42 = lean_io_error_to_string(x_41);
x_43 = 3;
x_44 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_43);
x_45 = lean_array_get_size(x_27);
x_46 = lean_array_push(x_27, x_44);
if (lean_is_scalar(x_28)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_28;
 lean_ctor_set_tag(x_47, 1);
}
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_15);
x_58 = lean_ctor_get(x_25, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_25, 1);
lean_inc(x_59);
lean_dec_ref(x_25);
x_5 = x_58;
x_6 = x_59;
x_7 = lean_box(0);
goto block_9;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_15);
lean_dec_ref(x_1);
x_60 = lean_ctor_get(x_20, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_20, 1);
lean_inc(x_61);
lean_dec_ref(x_20);
x_5 = x_60;
x_6 = x_61;
x_7 = lean_box(0);
goto block_9;
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_15);
lean_dec_ref(x_1);
x_62 = lean_ctor_get(x_18, 0);
lean_inc(x_62);
lean_dec_ref(x_18);
x_63 = lean_io_error_to_string(x_62);
x_64 = 3;
x_65 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_64);
x_66 = lean_array_get_size(x_3);
x_67 = lean_array_push(x_3, x_65);
x_5 = x_66;
x_6 = x_67;
x_7 = lean_box(0);
goto block_9;
}
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_15);
lean_dec_ref(x_1);
x_68 = lean_ctor_get(x_17, 0);
lean_inc(x_68);
lean_dec_ref(x_17);
x_69 = lean_io_error_to_string(x_68);
x_70 = 3;
x_71 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_70);
x_72 = lean_array_get_size(x_3);
x_73 = lean_array_push(x_3, x_71);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_75 = lean_ctor_get(x_14, 0);
lean_inc(x_75);
lean_dec_ref(x_14);
x_76 = l_Lake_CacheMap_load___closed__0;
x_77 = lean_string_append(x_1, x_76);
x_78 = lean_io_error_to_string(x_75);
x_79 = lean_string_append(x_77, x_78);
lean_dec_ref(x_78);
x_80 = 3;
x_81 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set_uint8(x_81, sizeof(void*)*1, x_80);
x_82 = lean_array_get_size(x_3);
x_83 = lean_array_push(x_3, x_81);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec_ref(x_1);
x_85 = lean_ctor_get(x_12, 0);
lean_inc(x_85);
lean_dec_ref(x_12);
x_86 = lean_io_error_to_string(x_85);
x_87 = 3;
x_88 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set_uint8(x_88, sizeof(void*)*1, x_87);
x_89 = lean_array_get_size(x_3);
x_90 = lean_array_push(x_3, x_88);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec_ref(x_1);
x_92 = lean_ctor_get(x_10, 0);
lean_inc(x_92);
lean_dec_ref(x_10);
x_93 = lean_io_error_to_string(x_92);
x_94 = 3;
x_95 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set_uint8(x_95, sizeof(void*)*1, x_94);
x_96 = lean_array_get_size(x_3);
x_97 = lean_array_push(x_3, x_95);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
block_9:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_updateFile_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_updateFile_spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__2(x_1, x_2, x_8, x_9, x_5, x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_updateFile_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_updateFile_spec__3(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__4(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_updateFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CacheMap_updateFile(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l_Lake_CacheMap_writeFile___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_CacheMap_schemaVersion___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_CacheMap_writeFile___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_CacheMap_writeFile___closed__0;
x_2 = l_Lean_Json_compress(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_writeFile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_createParentDirs(x_1);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; lean_object* x_7; 
lean_dec_ref(x_5);
x_6 = 1;
x_7 = lean_io_prim_handle_mk(x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = 1;
x_10 = lean_io_prim_handle_lock(x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec_ref(x_10);
x_11 = l_Lake_CacheMap_writeFile___closed__1;
x_12 = l_IO_FS_Handle_putStrLn(x_8, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec_ref(x_12);
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 0);
lean_dec(x_15);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get_size(x_14);
x_18 = lean_box(0);
x_19 = lean_nat_dec_lt(x_16, x_17);
if (x_19 == 0)
{
lean_dec(x_17);
lean_dec_ref(x_14);
lean_dec(x_8);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_18);
return x_2;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_17, x_17);
if (x_20 == 0)
{
lean_dec(x_17);
lean_dec_ref(x_14);
lean_dec(x_8);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_18);
return x_2;
}
else
{
size_t x_21; size_t x_22; lean_object* x_23; 
lean_free_object(x_2);
x_21 = 0;
x_22 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_23 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__2(x_8, x_14, x_21, x_22, x_18, x_3);
lean_dec_ref(x_14);
lean_dec(x_8);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
lean_dec(x_2);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_array_get_size(x_24);
x_27 = lean_box(0);
x_28 = lean_nat_dec_lt(x_25, x_26);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_26);
lean_dec_ref(x_24);
lean_dec(x_8);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_3);
return x_29;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_26, x_26);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_26);
lean_dec_ref(x_24);
lean_dec(x_8);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_3);
return x_31;
}
else
{
size_t x_32; size_t x_33; lean_object* x_34; 
x_32 = 0;
x_33 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_34 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__2(x_8, x_24, x_32, x_33, x_27, x_3);
lean_dec_ref(x_24);
lean_dec(x_8);
return x_34;
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_8);
lean_dec_ref(x_2);
x_35 = lean_ctor_get(x_12, 0);
lean_inc(x_35);
lean_dec_ref(x_12);
x_36 = lean_io_error_to_string(x_35);
x_37 = 3;
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_37);
x_39 = lean_array_get_size(x_3);
x_40 = lean_array_push(x_3, x_38);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_8);
lean_dec_ref(x_2);
x_42 = lean_ctor_get(x_10, 0);
lean_inc(x_42);
lean_dec_ref(x_10);
x_43 = lean_io_error_to_string(x_42);
x_44 = 3;
x_45 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_44);
x_46 = lean_array_get_size(x_3);
x_47 = lean_array_push(x_3, x_45);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec_ref(x_2);
x_49 = lean_ctor_get(x_7, 0);
lean_inc(x_49);
lean_dec_ref(x_7);
x_50 = l_Lake_CacheMap_load___closed__0;
x_51 = lean_string_append(x_1, x_50);
x_52 = lean_io_error_to_string(x_49);
x_53 = lean_string_append(x_51, x_52);
lean_dec_ref(x_52);
x_54 = 3;
x_55 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_54);
x_56 = lean_array_get_size(x_3);
x_57 = lean_array_push(x_3, x_55);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_59 = lean_ctor_get(x_5, 0);
lean_inc(x_59);
lean_dec_ref(x_5);
x_60 = lean_io_error_to_string(x_59);
x_61 = 3;
x_62 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_61);
x_63 = lean_array_get_size(x_3);
x_64 = lean_array_push(x_3, x_62);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_writeFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CacheMap_writeFile(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___redArg(uint64_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_unbox_uint64(x_4);
x_8 = lean_uint64_dec_eq(x_7, x_1);
if (x_8 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_10; 
lean_inc(x_5);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_5);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg(lean_object* x_1, uint64_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = 32;
x_6 = lean_uint64_shift_right(x_2, x_5);
x_7 = lean_uint64_xor(x_2, x_6);
x_8 = 16;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = lean_uint64_to_usize(x_10);
x_12 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_13 = 1;
x_14 = lean_usize_sub(x_12, x_13);
x_15 = lean_usize_land(x_11, x_14);
x_16 = lean_array_uget(x_3, x_15);
x_17 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___redArg(x_2, x_16);
lean_dec(x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0(lean_object* x_1, lean_object* x_2, uint64_t x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_get_x3f(uint64_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___redArg(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg(x_1, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_5 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0(x_1, x_2, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_get_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Lake_CacheMap_get_x3f(x_3, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_insertCore(uint64_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___redArg(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_insertCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_5 = l_Lake_CacheMap_insertCore(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___redArg(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_apply_1(x_1, x_3);
x_6 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___redArg(x_4, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_apply_1(x_2, x_4);
x_7 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___redArg(x_5, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_6 = l_Lake_CacheMap_insert___redArg(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint64_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_7 = l_Lake_CacheMap_insert(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_8 = lean_array_uget(x_1, x_2);
x_9 = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(x_4, x_8, x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_10;
x_5 = x_11;
goto _start;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_5);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 4);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1(x_1, x_6, x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(x_9, x_5, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_1 = x_12;
x_2 = x_7;
x_3 = x_13;
goto _start;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsupported output: ", 20, 20);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsupported output; ", 20, 20);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("art", 3, 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
case 1:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get_uint8(x_2, 0);
lean_dec_ref(x_2);
x_7 = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__0;
if (x_6 == 0)
{
lean_object* x_15; 
x_15 = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__1;
x_8 = x_15;
goto block_14;
}
else
{
lean_object* x_16; 
x_16 = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__2;
x_8 = x_16;
goto block_14;
}
block_14:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_string_append(x_7, x_8);
lean_dec_ref(x_8);
x_10 = 3;
x_11 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_10);
x_12 = lean_array_push(x_3, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
case 2:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_17);
lean_dec_ref(x_2);
x_18 = l_Lake_Hash_ofJsonNumber_x3f(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__3;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__1;
x_23 = lean_string_append(x_21, x_22);
x_24 = l_Lean_JsonNumber_toString(x_17);
x_25 = lean_string_append(x_23, x_24);
lean_dec_ref(x_24);
x_26 = 3;
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
x_28 = lean_array_push(x_3, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint64_t x_33; lean_object* x_34; lean_object* x_35; 
lean_dec_ref(x_17);
x_30 = lean_ctor_get(x_18, 0);
lean_inc(x_30);
lean_dec_ref(x_18);
x_31 = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__4;
x_32 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_unbox_uint64(x_30);
lean_dec(x_30);
lean_ctor_set_uint64(x_32, sizeof(void*)*1, x_33);
x_34 = lean_array_push(x_1, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_3);
return x_35;
}
}
case 3:
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_36);
lean_dec_ref(x_2);
x_37 = l_Lake_ArtifactDescr_ofFilePath_x3f(x_36);
lean_dec_ref(x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__0;
x_40 = lean_string_append(x_39, x_38);
lean_dec(x_38);
x_41 = 3;
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
x_43 = lean_array_push(x_3, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_37, 0);
lean_inc(x_45);
lean_dec_ref(x_37);
x_46 = lean_array_push(x_1, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_3);
return x_47;
}
}
case 4:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_48);
lean_dec_ref(x_2);
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_array_get_size(x_48);
x_51 = lean_nat_dec_lt(x_49, x_50);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec(x_50);
lean_dec_ref(x_48);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_1);
lean_ctor_set(x_52, 1, x_3);
return x_52;
}
else
{
uint8_t x_53; 
x_53 = lean_nat_dec_le(x_50, x_50);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_50);
lean_dec_ref(x_48);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_1);
lean_ctor_set(x_54, 1, x_3);
return x_54;
}
else
{
size_t x_55; size_t x_56; lean_object* x_57; 
x_55 = 0;
x_56 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_57 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0(x_48, x_55, x_56, x_1, x_3);
lean_dec_ref(x_48);
return x_57;
}
}
}
default: 
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_2, 0);
lean_inc(x_58);
lean_dec_ref(x_2);
x_59 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1(x_1, x_58, x_3);
return x_59;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0(x_1, x_7, x_8, x_4, x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_collectOutputDescrs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(x_1, x_6, x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_1 = x_9;
x_2 = x_7;
x_3 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_8 = lean_array_uget(x_1, x_2);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_collectOutputDescrs_spec__0(x_4, x_8, x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_10;
x_5 = x_11;
goto _start;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_5);
return x_15;
}
}
}
static lean_object* _init_l_Lake_CacheMap_collectOutputDescrs___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_collectOutputDescrs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_17; uint8_t x_18; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_5 = x_1;
} else {
 lean_dec_ref(x_1);
 x_5 = lean_box(0);
}
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lake_CacheMap_collectOutputDescrs___closed__0;
x_8 = lean_array_get_size(x_2);
x_17 = lean_array_get_size(x_4);
x_18 = lean_nat_dec_lt(x_6, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_dec_ref(x_4);
lean_inc_ref(x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_2);
x_9 = x_19;
x_10 = x_2;
x_11 = lean_box(0);
goto block_16;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_17, x_17);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_17);
lean_dec_ref(x_4);
lean_inc_ref(x_2);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_2);
x_9 = x_21;
x_10 = x_2;
x_11 = lean_box(0);
goto block_16;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = 0;
x_23 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_24 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1(x_4, x_22, x_23, x_7, x_2);
lean_dec_ref(x_4);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
x_9 = x_24;
x_10 = x_25;
x_11 = lean_box(0);
goto block_16;
}
}
block_16:
{
lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_12 = lean_array_get_size(x_10);
x_13 = lean_nat_dec_eq(x_8, x_12);
lean_dec(x_12);
x_14 = l_instDecidableNot___redArg(x_13);
if (x_14 == 0)
{
lean_dec_ref(x_10);
lean_dec(x_8);
lean_dec(x_5);
return x_9;
}
else
{
lean_object* x_15; 
lean_dec_ref(x_9);
if (lean_is_scalar(x_5)) {
 x_15 = lean_alloc_ctor(1, 2, 0);
} else {
 x_15 = x_5;
 lean_ctor_set_tag(x_15, 1);
}
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_collectOutputDescrs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_collectOutputDescrs_spec__0(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1(x_1, x_7, x_8, x_4, x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_collectOutputDescrs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_CacheMap_collectOutputDescrs(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_mk(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_st_mk_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_mk___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_CacheRef_mk(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_get_x3f(uint64_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_st_ref_take(x_2);
lean_inc_ref(x_4);
x_5 = lean_st_ref_set(x_2, x_4);
x_6 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg(x_4, x_1);
lean_dec_ref(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_get_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_5 = l_Lake_CacheRef_get_x3f(x_4, x_2);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___redArg(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_st_ref_take(x_4);
x_7 = lean_apply_1(x_1, x_3);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___redArg(x_6, x_2, x_7);
x_9 = lean_st_ref_set(x_4, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_st_ref_take(x_5);
x_8 = lean_apply_1(x_2, x_4);
x_9 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___redArg(x_7, x_3, x_8);
x_10 = lean_st_ref_set(x_5, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint64_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_7 = l_Lake_CacheRef_insert___redArg(x_1, x_6, x_3, x_4);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint64_t x_7; lean_object* x_8; 
x_7 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_8 = l_Lake_CacheRef_insert(x_1, x_2, x_7, x_4, x_5);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Cache_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instInhabitedCache_default___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_System_instInhabitedFilePath_default;
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedCache_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedCache_default___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedCache() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedCache_default___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_Cache_artifactDir___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("artifacts", 9, 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_artifactDir(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lake_Cache_artifactDir___closed__0;
x_3 = l_System_FilePath_join(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Cache_artifactPath___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_artifactPath(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = l_Lake_Cache_artifactDir___closed__0;
x_5 = l_System_FilePath_join(x_1, x_4);
x_6 = lean_string_utf8_byte_size(x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l_Lake_Hash_hex(x_2);
x_10 = l_Lake_Cache_artifactPath___closed__0;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_3);
x_13 = l_System_FilePath_join(x_5, x_12);
lean_dec_ref(x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lake_Hash_hex(x_2);
x_15 = l_System_FilePath_join(x_5, x_14);
lean_dec_ref(x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_artifactPath___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Lake_Cache_artifactPath(x_1, x_4, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
static lean_object* _init_l_Lake_Cache_getArtifact_x3f___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Cache_getArtifact_x3f___closed__1() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lake_Cache_getArtifact_x3f___closed__0;
x_3 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_4 = lean_ctor_get_uint64(x_2, sizeof(void*)*1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = l_Lake_Cache_artifactDir___closed__0;
x_7 = l_System_FilePath_join(x_1, x_6);
x_31 = lean_string_utf8_byte_size(x_5);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_dec_eq(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = l_Lake_Hash_hex(x_4);
x_35 = l_Lake_Cache_artifactPath___closed__0;
x_36 = lean_string_append(x_34, x_35);
x_37 = lean_string_append(x_36, x_5);
x_8 = x_37;
goto block_30;
}
else
{
lean_object* x_38; 
x_38 = l_Lake_Hash_hex(x_4);
x_8 = x_38;
goto block_30;
}
block_30:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_System_FilePath_join(x_7, x_8);
lean_dec_ref(x_8);
x_10 = lean_io_metadata(x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_13);
lean_dec(x_12);
lean_inc_ref(x_9);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_9);
lean_ctor_set(x_14, 3, x_13);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_16);
lean_dec(x_15);
lean_inc_ref(x_9);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_9);
lean_ctor_set(x_17, 2, x_9);
lean_ctor_set(x_17, 3, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_10, 0);
lean_dec(x_20);
x_21 = l_System_FilePath_pathExists(x_9);
if (x_21 == 0)
{
lean_object* x_22; 
lean_free_object(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_22 = lean_box(0);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lake_Cache_getArtifact_x3f___closed__1;
lean_inc_ref(x_9);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_9);
lean_ctor_set(x_24, 2, x_9);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set(x_10, 0, x_24);
return x_10;
}
}
else
{
uint8_t x_25; 
lean_dec(x_10);
x_25 = l_System_FilePath_pathExists(x_9);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_26 = lean_box(0);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = l_Lake_Cache_getArtifact_x3f___closed__1;
lean_inc_ref(x_9);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_9);
lean_ctor_set(x_28, 2, x_9);
lean_ctor_set(x_28, 3, x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Cache_getArtifact_x3f(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Cache_getArtifact___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("artifact not found in cache: ", 29, 29);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_4 = lean_ctor_get_uint64(x_2, sizeof(void*)*1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = l_Lake_Cache_artifactDir___closed__0;
x_7 = l_System_FilePath_join(x_1, x_6);
x_34 = lean_string_utf8_byte_size(x_5);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_nat_dec_eq(x_34, x_35);
lean_dec(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = l_Lake_Hash_hex(x_4);
x_38 = l_Lake_Cache_artifactPath___closed__0;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_string_append(x_39, x_5);
x_8 = x_40;
goto block_33;
}
else
{
lean_object* x_41; 
x_41 = l_Lake_Hash_hex(x_4);
x_8 = x_41;
goto block_33;
}
block_33:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_System_FilePath_join(x_7, x_8);
lean_dec_ref(x_8);
x_10 = lean_io_metadata(x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_13);
lean_dec(x_12);
lean_inc_ref(x_9);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_9);
lean_ctor_set(x_14, 3, x_13);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_16);
lean_dec(x_15);
lean_inc_ref(x_9);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_9);
lean_ctor_set(x_17, 2, x_9);
lean_ctor_set(x_17, 3, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_10, 0);
lean_dec(x_20);
x_21 = l_System_FilePath_pathExists(x_9);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec_ref(x_2);
x_22 = l_Lake_Cache_getArtifact___closed__0;
x_23 = lean_string_append(x_22, x_9);
lean_dec_ref(x_9);
lean_ctor_set(x_10, 0, x_23);
return x_10;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lake_Cache_getArtifact_x3f___closed__1;
lean_inc_ref(x_9);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_9);
lean_ctor_set(x_25, 2, x_9);
lean_ctor_set(x_25, 3, x_24);
lean_ctor_set_tag(x_10, 0);
lean_ctor_set(x_10, 0, x_25);
return x_10;
}
}
else
{
uint8_t x_26; 
lean_dec(x_10);
x_26 = l_System_FilePath_pathExists(x_9);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec_ref(x_2);
x_27 = l_Lake_Cache_getArtifact___closed__0;
x_28 = lean_string_append(x_27, x_9);
lean_dec_ref(x_9);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = l_Lake_Cache_getArtifact_x3f___closed__1;
lean_inc_ref(x_9);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_9);
lean_ctor_set(x_31, 2, x_9);
lean_ctor_set(x_31, 3, x_30);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Cache_getArtifact(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_4, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_4);
lean_dec_ref(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_fget_borrowed(x_3, x_4);
lean_inc_ref(x_2);
lean_inc(x_10);
x_11 = lean_apply_3(x_2, x_10, x_6, lean_box(0));
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_4, x_14);
lean_dec(x_4);
x_16 = lean_array_push(x_5, x_12);
x_4 = x_15;
x_5 = x_16;
x_6 = x_13;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0___redArg(x_3, x_4, x_5, x_6, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifactPaths___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_10 = lean_ctor_get_uint64(x_2, sizeof(void*)*1);
x_11 = lean_ctor_get(x_2, 0);
x_12 = l_Lake_Cache_artifactDir___closed__0;
x_13 = l_System_FilePath_join(x_1, x_12);
x_23 = lean_string_utf8_byte_size(x_11);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_eq(x_23, x_24);
lean_dec(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = l_Lake_Hash_hex(x_10);
x_27 = l_Lake_Cache_artifactPath___closed__0;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_string_append(x_28, x_11);
x_14 = x_29;
goto block_22;
}
else
{
lean_object* x_30; 
x_30 = l_Lake_Hash_hex(x_10);
x_14 = x_30;
goto block_22;
}
block_9:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
block_22:
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_System_FilePath_join(x_13, x_14);
lean_dec_ref(x_14);
x_16 = l_System_FilePath_pathExists(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_17 = l_Lake_Cache_getArtifact___closed__0;
x_18 = lean_string_append(x_17, x_15);
x_19 = 3;
x_20 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_19);
x_21 = lean_array_push(x_3, x_20);
x_5 = x_15;
x_6 = x_21;
x_7 = lean_box(0);
goto block_9;
}
else
{
x_5 = x_15;
x_6 = x_3;
x_7 = lean_box(0);
goto block_9;
}
}
}
}
static lean_object* _init_l_Lake_Cache_getArtifactPaths___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifactPaths(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_alloc_closure((void*)(l_Lake_Cache_getArtifactPaths___lam__0___boxed), 4, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_array_get_size(x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lake_Cache_getArtifactPaths___closed__0;
lean_inc_ref(x_3);
x_9 = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0___redArg(x_6, x_5, x_2, x_7, x_8, x_3);
lean_dec(x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_array_get_size(x_3);
lean_dec_ref(x_3);
x_12 = lean_array_get_size(x_10);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_12);
x_14 = l_instDecidableNot___redArg(x_13);
if (x_14 == 0)
{
lean_dec(x_11);
lean_dec(x_10);
return x_9;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_9, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_9, 0);
lean_dec(x_17);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_11);
return x_9;
}
else
{
lean_object* x_18; 
lean_dec(x_9);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
}
}
else
{
lean_dec_ref(x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00Lake_Cache_getArtifactPaths_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_5);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifactPaths___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Cache_getArtifactPaths___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifactPaths___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Cache_getArtifactPaths(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l_Lake_Cache_outputsDir___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("outputs", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_outputsDir(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lake_Cache_outputsDir___closed__0;
x_3 = l_System_FilePath_join(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Cache_outputsFile___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".json", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_outputsFile(lean_object* x_1, lean_object* x_2, uint64_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Lake_Cache_outputsDir___closed__0;
x_5 = l_System_FilePath_join(x_1, x_4);
x_6 = l_System_FilePath_join(x_5, x_2);
x_7 = l_Lake_Hash_hex(x_3);
x_8 = l_Lake_Cache_outputsFile___closed__0;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_System_FilePath_join(x_6, x_9);
lean_dec_ref(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_outputsFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_5 = l_Lake_Cache_outputsFile(x_1, x_2, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputsCore(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = l_Lake_Cache_outputsDir___closed__0;
x_7 = l_System_FilePath_join(x_1, x_6);
x_8 = l_System_FilePath_join(x_7, x_2);
x_9 = l_Lake_Hash_hex(x_3);
x_10 = l_Lake_Cache_outputsFile___closed__0;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_System_FilePath_join(x_8, x_11);
lean_dec_ref(x_11);
x_13 = l_Lake_createParentDirs(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_13);
x_14 = l_Lean_Json_compress(x_4);
x_15 = l_IO_FS_writeFile(x_12, x_14);
lean_dec_ref(x_14);
lean_dec_ref(x_12);
return x_15;
}
else
{
lean_dec_ref(x_12);
lean_dec(x_4);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputsCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint64_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_7 = l_Lake_Cache_writeOutputsCore(x_1, x_2, x_6, x_4);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint64_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_apply_1(x_1, x_5);
x_8 = l_Lake_Cache_writeOutputsCore(x_2, x_3, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint64_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_apply_1(x_2, x_6);
x_9 = l_Lake_Cache_writeOutputsCore(x_3, x_4, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint64_t x_7; lean_object* x_8; 
x_7 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_8 = l_Lake_Cache_writeOutputs___redArg(x_1, x_2, x_3, x_7, x_5);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint64_t x_8; lean_object* x_9; 
x_8 = lean_unbox_uint64(x_5);
lean_dec(x_5);
x_9 = l_Lake_Cache_writeOutputs(x_1, x_2, x_3, x_4, x_8, x_6);
lean_dec_ref(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; 
lean_dec_ref(x_1);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
lean_dec_ref(x_4);
x_10 = lean_unbox_uint64(x_7);
lean_dec(x_7);
lean_inc_ref(x_1);
x_11 = l_Lake_Cache_writeOutputsCore(x_1, x_2, x_10, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_3 = x_12;
x_4 = x_9;
goto _start;
}
else
{
lean_dec(x_9);
lean_dec_ref(x_1);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_4, x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_array_uget(x_3, x_4);
x_10 = lean_box(0);
lean_inc_ref(x_1);
x_11 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0(x_1, x_2, x_10, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = 1;
x_14 = lean_usize_add(x_4, x_13);
x_4 = x_14;
x_6 = x_12;
goto _start;
}
else
{
lean_dec_ref(x_1);
return x_11;
}
}
else
{
lean_object* x_16; 
lean_dec_ref(x_1);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_6);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeMap(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get_size(x_5);
x_8 = lean_box(0);
x_9 = lean_nat_dec_lt(x_6, x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec_ref(x_1);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_7, x_7);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_7);
lean_dec_ref(x_1);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_8);
return x_12;
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1(x_1, x_2, x_5, x_13, x_14, x_8);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1(x_1, x_2, x_3, x_8, x_9, x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeMap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Cache_writeMap(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l_Lake_Cache_readOutputs_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": invalid JSON: ", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lake_Cache_readOutputs_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": read failed: ", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_readOutputs_x3f(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = l_Lake_Cache_outputsDir___closed__0;
x_7 = l_System_FilePath_join(x_1, x_6);
x_8 = l_System_FilePath_join(x_7, x_2);
x_9 = l_Lake_Hash_hex(x_3);
x_10 = l_Lake_Cache_outputsFile___closed__0;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_System_FilePath_join(x_8, x_11);
lean_dec_ref(x_11);
x_13 = l_IO_FS_readFile(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = l_Lean_Json_parse(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l_Lake_Cache_readOutputs_x3f___closed__0;
x_18 = lean_string_append(x_12, x_17);
x_19 = lean_string_append(x_18, x_16);
lean_dec(x_16);
x_20 = 2;
x_21 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
x_22 = lean_array_push(x_4, x_21);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec_ref(x_12);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_15);
lean_ctor_set(x_26, 1, x_4);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_15, 0);
lean_inc(x_27);
lean_dec(x_15);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_4);
return x_29;
}
}
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_13, 0);
lean_inc(x_30);
lean_dec_ref(x_13);
if (lean_obj_tag(x_30) == 11)
{
lean_object* x_31; lean_object* x_32; 
lean_dec_ref(x_30);
lean_dec_ref(x_12);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_4);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = l_Lake_Cache_readOutputs_x3f___closed__1;
x_34 = lean_string_append(x_12, x_33);
x_35 = lean_io_error_to_string(x_30);
x_36 = lean_string_append(x_34, x_35);
lean_dec_ref(x_35);
x_37 = 3;
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_37);
x_39 = lean_array_get_size(x_4);
x_40 = lean_array_push(x_4, x_38);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_readOutputs_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint64_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_7 = l_Lake_Cache_readOutputs_x3f(x_1, x_2, x_6, x_4);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l_Lake_Cache_revisionDir___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("revisions", 9, 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_revisionDir(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lake_Cache_revisionDir___closed__0;
x_3 = l_System_FilePath_join(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Cache_revisionPath___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".jsonl", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_revisionPath(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = l_Lake_Cache_revisionDir___closed__0;
x_5 = l_System_FilePath_join(x_1, x_4);
x_6 = l_System_FilePath_join(x_5, x_2);
x_7 = l_Lake_Cache_revisionPath___closed__0;
x_8 = lean_string_append(x_3, x_7);
x_9 = l_System_FilePath_join(x_6, x_8);
lean_dec_ref(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_revisionPath___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Cache_revisionPath(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__0() {
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
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("curl", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-s", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--aws-sigv4", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("aws:amz:auto:s3", 15, 15);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--user", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-X", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PUT", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-T", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-H", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Content-Type: ", 14, 14);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(12u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__2;
x_2 = l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__3;
x_2 = l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4;
x_2 = l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__13;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5;
x_2 = l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__14;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_11 = l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__0;
x_12 = l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__1;
x_13 = l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6;
x_14 = l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__7;
x_15 = l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__8;
x_16 = l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9;
x_17 = l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10;
x_18 = lean_string_append(x_17, x_2);
x_19 = l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__15;
x_20 = lean_array_push(x_19, x_4);
x_21 = lean_array_push(x_20, x_13);
x_22 = lean_array_push(x_21, x_14);
x_23 = lean_array_push(x_22, x_15);
x_24 = lean_array_push(x_23, x_1);
x_25 = lean_array_push(x_24, x_3);
x_26 = lean_array_push(x_25, x_16);
x_27 = lean_array_push(x_26, x_18);
x_28 = lean_box(0);
x_29 = lean_unsigned_to_nat(0u);
x_30 = l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16;
x_31 = 1;
x_32 = 0;
x_33 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_33, 0, x_11);
lean_ctor_set(x_33, 1, x_12);
lean_ctor_set(x_33, 2, x_27);
lean_ctor_set(x_33, 3, x_28);
lean_ctor_set(x_33, 4, x_30);
lean_ctor_set_uint8(x_33, sizeof(void*)*5, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*5 + 1, x_32);
x_34 = l_Lake_proc(x_33, x_31, x_30);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec_ref(x_34);
x_37 = lean_array_get_size(x_36);
x_38 = lean_nat_dec_lt(x_29, x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec_ref(x_5);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_35);
return x_39;
}
else
{
uint8_t x_40; 
x_40 = lean_nat_dec_le(x_37, x_37);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec_ref(x_5);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_35);
return x_41;
}
else
{
lean_object* x_42; size_t x_43; size_t x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_box(0);
x_43 = 0;
x_44 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_45 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(x_36, x_43, x_44, x_42, x_5);
lean_dec(x_36);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set(x_45, 0, x_35);
return x_45;
}
else
{
lean_object* x_48; 
lean_dec(x_45);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_35);
return x_48;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_34, 1);
lean_inc(x_49);
lean_dec_ref(x_34);
x_50 = lean_array_get_size(x_49);
x_51 = lean_nat_dec_lt(x_29, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec_ref(x_5);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
else
{
uint8_t x_54; 
x_54 = lean_nat_dec_le(x_50, x_50);
if (x_54 == 0)
{
lean_dec(x_50);
lean_dec(x_49);
lean_dec_ref(x_5);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_55; size_t x_56; size_t x_57; lean_object* x_58; 
x_55 = lean_box(0);
x_56 = 0;
x_57 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_58 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(x_49, x_56, x_57, x_55, x_5);
lean_dec(x_49);
lean_dec_ref(x_58);
x_7 = lean_box(0);
goto block_10;
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Config_Cache_0__Lake_uploadS3(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_CacheService_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_CacheService_reservoirService___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_reservoirService(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_3 = l_Lake_CacheService_reservoirService___closed__0;
x_4 = 1;
x_5 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*4, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*4 + 1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_reservoirService___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
x_4 = l_Lake_CacheService_reservoirService(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadService(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = 0;
x_5 = l_Lake_CacheService_reservoirService___closed__0;
x_6 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4 + 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadService(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_3 = l_Lake_CacheService_reservoirService___closed__0;
x_4 = 0;
x_5 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*4, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*4 + 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtsService(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_2 = l_Lake_CacheService_reservoirService___closed__0;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*4 + 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_withRepoScope(lean_object* x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 1, x_2);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*4 + 1, x_2);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_withRepoScope___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
x_4 = l_Lake_CacheService_withRepoScope(x_1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_CacheService_artifactContentType___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("application/vnd.reservoir.artifact", 34, 34);
return x_1;
}
}
static lean_object* _init_l_Lake_CacheService_artifactContentType() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_CacheService_artifactContentType___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_splitAux___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_string_utf8_at_end(x_1, x_3);
if (x_5 == 0)
{
uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_6 = lean_string_utf8_get(x_1, x_3);
x_7 = 47;
x_8 = lean_uint32_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_string_utf8_next(x_1, x_3);
x_12 = lean_string_utf8_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
lean_inc(x_11);
x_2 = x_11;
x_3 = x_11;
x_4 = x_13;
goto _start;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_string_utf8_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
x_17 = l_List_reverse___redArg(x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint32_t x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lake_uriEncode(x_3, x_1);
x_6 = 47;
x_7 = lean_string_push(x_5, x_6);
x_1 = x_7;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_box(0);
x_5 = l_String_splitAux___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0(x_2, x_3, x_3, x_4);
x_6 = l_List_foldl___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1(x_1, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_splitAux___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_splitAux___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".art", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(uint64_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
x_5 = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0;
x_6 = lean_string_append(x_4, x_5);
x_7 = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(x_6, x_3);
x_8 = l_Lake_Hash_hex(x_1);
x_9 = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_string_append(x_7, x_10);
lean_dec_ref(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_5 = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(x_4, x_2, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
static lean_object* _init_l_Lake_CacheService_artifactUrl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("artifacts/", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_CacheService_artifactUrl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/packages/", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_CacheService_artifactUrl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/repositories/", 14, 14);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_artifactUrl(uint64_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_13; 
x_13 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(x_1, x_2, x_3);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_16);
lean_dec_ref(x_2);
x_17 = l_Lake_CacheService_artifactUrl___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_4 = x_18;
goto block_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_19);
lean_dec_ref(x_2);
x_20 = l_Lake_CacheService_artifactUrl___closed__2;
x_21 = lean_string_append(x_19, x_20);
x_4 = x_21;
goto block_12;
}
}
block_12:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(x_4, x_3);
x_6 = l_Lake_CacheService_artifactUrl___closed__0;
x_7 = l_Lake_Hash_hex(x_1);
x_8 = lean_string_append(x_6, x_7);
lean_dec_ref(x_7);
x_9 = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_string_append(x_5, x_10);
lean_dec_ref(x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_artifactUrl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_5 = l_Lake_CacheService_artifactUrl(x_4, x_2, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
static lean_object* _init_l_Lake_CacheService_downloadArtifact___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": downloaded artifact does not have the expected hash", 53, 53);
return x_1;
}
}
static lean_object* _init_l_Lake_CacheService_downloadArtifact___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": downloading artifact ", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lake_CacheService_downloadArtifact___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n  local path: ", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_CacheService_downloadArtifact___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n  remote URL: ", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_CacheService_downloadArtifact___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_CacheMap_parse___closed__5;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static uint8_t _init_l_Lake_CacheService_downloadArtifact___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_Lake_CacheService_downloadArtifact___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_lt(x_2, x_1);
return x_3;
}
}
static uint8_t _init_l_Lake_CacheService_downloadArtifact___closed__6() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lake_CacheService_downloadArtifact___closed__4;
x_2 = lean_nat_dec_le(x_1, x_1);
return x_2;
}
}
static size_t _init_l_Lake_CacheService_downloadArtifact___closed__7() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Lake_CacheService_downloadArtifact___closed__4;
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; uint64_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_13 = lean_ctor_get(x_1, 0);
x_81 = l_Lake_CacheService_artifactUrl(x_12, x_3, x_4);
x_125 = l_Lake_Cache_artifactDir___closed__0;
x_126 = l_System_FilePath_join(x_2, x_125);
x_138 = lean_string_utf8_byte_size(x_13);
x_139 = lean_unsigned_to_nat(0u);
x_140 = lean_nat_dec_eq(x_138, x_139);
lean_dec(x_138);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_141 = l_Lake_Hash_hex(x_12);
x_142 = l_Lake_Cache_artifactPath___closed__0;
x_143 = lean_string_append(x_141, x_142);
x_144 = lean_string_append(x_143, x_13);
x_127 = x_144;
goto block_137;
}
else
{
lean_object* x_145; 
x_145 = l_Lake_Hash_hex(x_12);
x_127 = x_145;
goto block_137;
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
block_80:
{
lean_object* x_16; 
x_16 = l_Lake_computeBinFileHash(x_14);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint64_t x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_unbox_uint64(x_18);
lean_dec(x_18);
x_20 = lean_uint64_dec_eq(x_19, x_12);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_free_object(x_16);
x_21 = l_Lake_CacheService_downloadArtifact___closed__0;
lean_inc_ref(x_14);
x_22 = lean_string_append(x_14, x_21);
x_23 = 3;
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_23);
lean_inc_ref(x_6);
x_25 = lean_apply_2(x_6, x_24, lean_box(0));
x_26 = lean_io_remove_file(x_14);
lean_dec_ref(x_14);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec_ref(x_6);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set_tag(x_26, 1);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_26);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_io_error_to_string(x_33);
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_23);
x_36 = lean_apply_2(x_6, x_35, lean_box(0));
x_37 = lean_box(0);
lean_ctor_set(x_26, 0, x_37);
return x_26;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_26, 0);
lean_inc(x_38);
lean_dec(x_26);
x_39 = lean_io_error_to_string(x_38);
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_23);
x_41 = lean_apply_2(x_6, x_40, lean_box(0));
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; 
lean_dec_ref(x_14);
lean_dec_ref(x_6);
x_44 = lean_box(0);
lean_ctor_set(x_16, 0, x_44);
return x_16;
}
}
else
{
lean_object* x_45; uint64_t x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_16, 0);
lean_inc(x_45);
lean_dec(x_16);
x_46 = lean_unbox_uint64(x_45);
lean_dec(x_45);
x_47 = lean_uint64_dec_eq(x_46, x_12);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = l_Lake_CacheService_downloadArtifact___closed__0;
lean_inc_ref(x_14);
x_49 = lean_string_append(x_14, x_48);
x_50 = 3;
x_51 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_50);
lean_inc_ref(x_6);
x_52 = lean_apply_2(x_6, x_51, lean_box(0));
x_53 = lean_io_remove_file(x_14);
lean_dec_ref(x_14);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec_ref(x_6);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_54 = x_53;
} else {
 lean_dec_ref(x_53);
 x_54 = lean_box(0);
}
x_55 = lean_box(0);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(1, 1, 0);
} else {
 x_56 = x_54;
 lean_ctor_set_tag(x_56, 1);
}
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_53, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_58 = x_53;
} else {
 lean_dec_ref(x_53);
 x_58 = lean_box(0);
}
x_59 = lean_io_error_to_string(x_57);
x_60 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_50);
x_61 = lean_apply_2(x_6, x_60, lean_box(0));
x_62 = lean_box(0);
if (lean_is_scalar(x_58)) {
 x_63 = lean_alloc_ctor(1, 1, 0);
} else {
 x_63 = x_58;
}
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec_ref(x_14);
lean_dec_ref(x_6);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec_ref(x_14);
x_66 = !lean_is_exclusive(x_16);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_16, 0);
x_68 = lean_io_error_to_string(x_67);
x_69 = 3;
x_70 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set_uint8(x_70, sizeof(void*)*1, x_69);
x_71 = lean_apply_2(x_6, x_70, lean_box(0));
x_72 = lean_box(0);
lean_ctor_set(x_16, 0, x_72);
return x_16;
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_73 = lean_ctor_get(x_16, 0);
lean_inc(x_73);
lean_dec(x_16);
x_74 = lean_io_error_to_string(x_73);
x_75 = 3;
x_76 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*1, x_75);
x_77 = lean_apply_2(x_6, x_76, lean_box(0));
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
}
}
block_118:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_84 = l_Lake_CacheService_downloadArtifact___closed__1;
x_85 = lean_string_append(x_4, x_84);
x_86 = l_Lake_Hash_hex(x_12);
x_87 = lean_string_append(x_85, x_86);
lean_dec_ref(x_86);
x_88 = l_Lake_CacheService_downloadArtifact___closed__2;
x_89 = lean_string_append(x_87, x_88);
x_90 = lean_string_append(x_89, x_82);
x_91 = l_Lake_CacheService_downloadArtifact___closed__3;
x_92 = lean_string_append(x_90, x_91);
x_93 = lean_string_append(x_92, x_81);
x_94 = 1;
x_95 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set_uint8(x_95, sizeof(void*)*1, x_94);
lean_inc_ref(x_6);
x_96 = lean_apply_2(x_6, x_95, lean_box(0));
x_97 = lean_unsigned_to_nat(0u);
x_98 = l_Lake_Cache_getArtifactPaths___closed__0;
lean_inc_ref(x_82);
x_99 = l_Lake_download(x_81, x_82, x_98, x_98);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec_ref(x_99);
x_101 = lean_array_get_size(x_100);
x_102 = lean_nat_dec_lt(x_97, x_101);
if (x_102 == 0)
{
lean_dec(x_101);
lean_dec(x_100);
x_14 = x_82;
x_15 = lean_box(0);
goto block_80;
}
else
{
uint8_t x_103; 
x_103 = lean_nat_dec_le(x_101, x_101);
if (x_103 == 0)
{
lean_dec(x_101);
lean_dec(x_100);
x_14 = x_82;
x_15 = lean_box(0);
goto block_80;
}
else
{
lean_object* x_104; size_t x_105; size_t x_106; lean_object* x_107; 
x_104 = lean_box(0);
x_105 = 0;
x_106 = lean_usize_of_nat(x_101);
lean_dec(x_101);
lean_inc_ref(x_6);
x_107 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(x_100, x_105, x_106, x_104, x_6);
lean_dec(x_100);
lean_dec_ref(x_107);
x_14 = x_82;
x_15 = lean_box(0);
goto block_80;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; 
lean_dec_ref(x_82);
x_108 = lean_ctor_get(x_99, 1);
lean_inc(x_108);
lean_dec_ref(x_99);
x_109 = lean_array_get_size(x_108);
x_110 = lean_nat_dec_lt(x_97, x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_109);
lean_dec(x_108);
lean_dec_ref(x_6);
x_111 = lean_box(0);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_111);
return x_112;
}
else
{
uint8_t x_113; 
x_113 = lean_nat_dec_le(x_109, x_109);
if (x_113 == 0)
{
lean_dec(x_109);
lean_dec(x_108);
lean_dec_ref(x_6);
x_8 = lean_box(0);
goto block_11;
}
else
{
lean_object* x_114; size_t x_115; size_t x_116; lean_object* x_117; 
x_114 = lean_box(0);
x_115 = 0;
x_116 = lean_usize_of_nat(x_109);
lean_dec(x_109);
x_117 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(x_108, x_115, x_116, x_114, x_6);
lean_dec(x_108);
lean_dec_ref(x_117);
x_8 = lean_box(0);
goto block_11;
}
}
}
}
block_124:
{
if (x_120 == 0)
{
x_82 = x_119;
x_83 = lean_box(0);
goto block_118;
}
else
{
if (x_5 == 0)
{
lean_object* x_122; lean_object* x_123; 
lean_dec_ref(x_119);
lean_dec_ref(x_81);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
else
{
x_82 = x_119;
x_83 = lean_box(0);
goto block_118;
}
}
}
block_137:
{
lean_object* x_128; uint8_t x_129; lean_object* x_130; uint8_t x_131; 
x_128 = l_System_FilePath_join(x_126, x_127);
lean_dec_ref(x_127);
x_129 = l_System_FilePath_pathExists(x_128);
x_130 = l_Lake_CacheMap_parse___closed__5;
x_131 = l_Lake_CacheService_downloadArtifact___closed__5;
if (x_131 == 0)
{
x_119 = x_128;
x_120 = x_129;
x_121 = lean_box(0);
goto block_124;
}
else
{
uint8_t x_132; 
x_132 = l_Lake_CacheService_downloadArtifact___closed__6;
if (x_132 == 0)
{
x_119 = x_128;
x_120 = x_129;
x_121 = lean_box(0);
goto block_124;
}
else
{
lean_object* x_133; size_t x_134; size_t x_135; lean_object* x_136; 
x_133 = lean_box(0);
x_134 = 0;
x_135 = l_Lake_CacheService_downloadArtifact___closed__7;
lean_inc_ref(x_6);
x_136 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(x_130, x_134, x_135, x_133, x_6);
lean_dec_ref(x_136);
x_119 = x_128;
x_120 = x_129;
x_121 = lean_box(0);
goto block_124;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
x_9 = l_Lake_CacheService_downloadArtifact(x_1, x_2, x_3, x_4, x_8, x_6);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact___at___00Lake_CacheService_downloadArtifacts___elam__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
lean_object* x_8; uint64_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_12 = lean_ctor_get_uint64(x_2, sizeof(void*)*1);
x_13 = lean_ctor_get(x_2, 0);
x_81 = l_Lake_CacheService_artifactUrl(x_12, x_4, x_5);
x_125 = l_Lake_Cache_artifactDir___closed__0;
x_126 = l_System_FilePath_join(x_3, x_125);
x_138 = lean_string_utf8_byte_size(x_13);
x_139 = lean_unsigned_to_nat(0u);
x_140 = lean_nat_dec_eq(x_138, x_139);
lean_dec(x_138);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_141 = l_Lake_Hash_hex(x_12);
x_142 = l_Lake_Cache_artifactPath___closed__0;
x_143 = lean_string_append(x_141, x_142);
x_144 = lean_string_append(x_143, x_13);
x_127 = x_144;
goto block_137;
}
else
{
lean_object* x_145; 
x_145 = l_Lake_Hash_hex(x_12);
x_127 = x_145;
goto block_137;
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
block_80:
{
lean_object* x_16; 
x_16 = l_Lake_computeBinFileHash(x_14);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint64_t x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_unbox_uint64(x_18);
lean_dec(x_18);
x_20 = lean_uint64_dec_eq(x_19, x_12);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_free_object(x_16);
x_21 = l_Lake_CacheService_downloadArtifact___closed__0;
lean_inc_ref(x_14);
x_22 = lean_string_append(x_14, x_21);
x_23 = 3;
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_23);
lean_inc_ref(x_1);
x_25 = lean_apply_2(x_1, x_24, lean_box(0));
x_26 = lean_io_remove_file(x_14);
lean_dec_ref(x_14);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec_ref(x_1);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set_tag(x_26, 1);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_26);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_io_error_to_string(x_33);
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_23);
x_36 = lean_apply_2(x_1, x_35, lean_box(0));
x_37 = lean_box(0);
lean_ctor_set(x_26, 0, x_37);
return x_26;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_26, 0);
lean_inc(x_38);
lean_dec(x_26);
x_39 = lean_io_error_to_string(x_38);
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_23);
x_41 = lean_apply_2(x_1, x_40, lean_box(0));
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; 
lean_dec_ref(x_14);
lean_dec_ref(x_1);
x_44 = lean_box(0);
lean_ctor_set(x_16, 0, x_44);
return x_16;
}
}
else
{
lean_object* x_45; uint64_t x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_16, 0);
lean_inc(x_45);
lean_dec(x_16);
x_46 = lean_unbox_uint64(x_45);
lean_dec(x_45);
x_47 = lean_uint64_dec_eq(x_46, x_12);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = l_Lake_CacheService_downloadArtifact___closed__0;
lean_inc_ref(x_14);
x_49 = lean_string_append(x_14, x_48);
x_50 = 3;
x_51 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_50);
lean_inc_ref(x_1);
x_52 = lean_apply_2(x_1, x_51, lean_box(0));
x_53 = lean_io_remove_file(x_14);
lean_dec_ref(x_14);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec_ref(x_1);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_54 = x_53;
} else {
 lean_dec_ref(x_53);
 x_54 = lean_box(0);
}
x_55 = lean_box(0);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(1, 1, 0);
} else {
 x_56 = x_54;
 lean_ctor_set_tag(x_56, 1);
}
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_53, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_58 = x_53;
} else {
 lean_dec_ref(x_53);
 x_58 = lean_box(0);
}
x_59 = lean_io_error_to_string(x_57);
x_60 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_50);
x_61 = lean_apply_2(x_1, x_60, lean_box(0));
x_62 = lean_box(0);
if (lean_is_scalar(x_58)) {
 x_63 = lean_alloc_ctor(1, 1, 0);
} else {
 x_63 = x_58;
}
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec_ref(x_14);
lean_dec_ref(x_1);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec_ref(x_14);
x_66 = !lean_is_exclusive(x_16);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_16, 0);
x_68 = lean_io_error_to_string(x_67);
x_69 = 3;
x_70 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set_uint8(x_70, sizeof(void*)*1, x_69);
x_71 = lean_apply_2(x_1, x_70, lean_box(0));
x_72 = lean_box(0);
lean_ctor_set(x_16, 0, x_72);
return x_16;
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_73 = lean_ctor_get(x_16, 0);
lean_inc(x_73);
lean_dec(x_16);
x_74 = lean_io_error_to_string(x_73);
x_75 = 3;
x_76 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*1, x_75);
x_77 = lean_apply_2(x_1, x_76, lean_box(0));
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
}
}
block_118:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_84 = l_Lake_CacheService_downloadArtifact___closed__1;
x_85 = lean_string_append(x_5, x_84);
x_86 = l_Lake_Hash_hex(x_12);
x_87 = lean_string_append(x_85, x_86);
lean_dec_ref(x_86);
x_88 = l_Lake_CacheService_downloadArtifact___closed__2;
x_89 = lean_string_append(x_87, x_88);
x_90 = lean_string_append(x_89, x_82);
x_91 = l_Lake_CacheService_downloadArtifact___closed__3;
x_92 = lean_string_append(x_90, x_91);
x_93 = lean_string_append(x_92, x_81);
x_94 = 1;
x_95 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set_uint8(x_95, sizeof(void*)*1, x_94);
lean_inc_ref(x_1);
x_96 = lean_apply_2(x_1, x_95, lean_box(0));
x_97 = lean_unsigned_to_nat(0u);
x_98 = l_Lake_Cache_getArtifactPaths___closed__0;
lean_inc_ref(x_82);
x_99 = l_Lake_download(x_81, x_82, x_98, x_98);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec_ref(x_99);
x_101 = lean_array_get_size(x_100);
x_102 = lean_nat_dec_lt(x_97, x_101);
if (x_102 == 0)
{
lean_dec(x_101);
lean_dec(x_100);
x_14 = x_82;
x_15 = lean_box(0);
goto block_80;
}
else
{
uint8_t x_103; 
x_103 = lean_nat_dec_le(x_101, x_101);
if (x_103 == 0)
{
lean_dec(x_101);
lean_dec(x_100);
x_14 = x_82;
x_15 = lean_box(0);
goto block_80;
}
else
{
lean_object* x_104; size_t x_105; size_t x_106; lean_object* x_107; 
x_104 = lean_box(0);
x_105 = 0;
x_106 = lean_usize_of_nat(x_101);
lean_dec(x_101);
lean_inc_ref(x_1);
x_107 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(x_100, x_105, x_106, x_104, x_1);
lean_dec(x_100);
lean_dec_ref(x_107);
x_14 = x_82;
x_15 = lean_box(0);
goto block_80;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; 
lean_dec_ref(x_82);
x_108 = lean_ctor_get(x_99, 1);
lean_inc(x_108);
lean_dec_ref(x_99);
x_109 = lean_array_get_size(x_108);
x_110 = lean_nat_dec_lt(x_97, x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_109);
lean_dec(x_108);
lean_dec_ref(x_1);
x_111 = lean_box(0);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_111);
return x_112;
}
else
{
uint8_t x_113; 
x_113 = lean_nat_dec_le(x_109, x_109);
if (x_113 == 0)
{
lean_dec(x_109);
lean_dec(x_108);
lean_dec_ref(x_1);
x_8 = lean_box(0);
goto block_11;
}
else
{
lean_object* x_114; size_t x_115; size_t x_116; lean_object* x_117; 
x_114 = lean_box(0);
x_115 = 0;
x_116 = lean_usize_of_nat(x_109);
lean_dec(x_109);
x_117 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(x_108, x_115, x_116, x_114, x_1);
lean_dec(x_108);
lean_dec_ref(x_117);
x_8 = lean_box(0);
goto block_11;
}
}
}
}
block_124:
{
if (x_120 == 0)
{
x_82 = x_119;
x_83 = lean_box(0);
goto block_118;
}
else
{
if (x_6 == 0)
{
lean_object* x_122; lean_object* x_123; 
lean_dec_ref(x_119);
lean_dec_ref(x_81);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
else
{
x_82 = x_119;
x_83 = lean_box(0);
goto block_118;
}
}
}
block_137:
{
lean_object* x_128; uint8_t x_129; lean_object* x_130; uint8_t x_131; 
x_128 = l_System_FilePath_join(x_126, x_127);
lean_dec_ref(x_127);
x_129 = l_System_FilePath_pathExists(x_128);
x_130 = l_Lake_CacheMap_parse___closed__5;
x_131 = l_Lake_CacheService_downloadArtifact___closed__5;
if (x_131 == 0)
{
x_119 = x_128;
x_120 = x_129;
x_121 = lean_box(0);
goto block_124;
}
else
{
uint8_t x_132; 
x_132 = l_Lake_CacheService_downloadArtifact___closed__6;
if (x_132 == 0)
{
x_119 = x_128;
x_120 = x_129;
x_121 = lean_box(0);
goto block_124;
}
else
{
lean_object* x_133; size_t x_134; size_t x_135; lean_object* x_136; 
x_133 = lean_box(0);
x_134 = 0;
x_135 = l_Lake_CacheService_downloadArtifact___closed__7;
lean_inc_ref(x_1);
x_136 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(x_130, x_134, x_135, x_133, x_1);
lean_dec_ref(x_136);
x_119 = x_128;
x_120 = x_129;
x_121 = lean_box(0);
goto block_124;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___elam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_CacheService_downloadArtifact___at___00Lake_CacheService_downloadArtifacts___elam__0_spec__0(x_7, x_6, x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
x_12 = lean_box(x_5);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
x_13 = lean_box(x_5);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_9, 0);
lean_dec(x_16);
x_17 = 0;
x_18 = lean_box(x_17);
lean_ctor_set_tag(x_9, 0);
lean_ctor_set(x_9, 0, x_18);
return x_9;
}
else
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_9);
x_19 = 0;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_CacheService_downloadArtifact___at___00Lake_CacheService_downloadArtifacts___elam__0_spec__0(x_1, x_7, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
x_12 = lean_box(x_6);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
x_13 = lean_box(x_6);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_9, 0);
lean_dec(x_16);
x_17 = 0;
x_18 = lean_box(x_17);
lean_ctor_set_tag(x_9, 0);
lean_ctor_set(x_9, 0, x_18);
return x_9;
}
else
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_9);
x_19 = 0;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, size_t x_6, size_t x_7, uint8_t x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_6, x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; uint8_t x_17; 
x_12 = lean_array_uget(x_5, x_6);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
lean_inc_ref(x_9);
x_13 = l_Lake_CacheService_downloadArtifacts___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__0_spec__0(x_9, x_1, x_2, x_3, x_4, x_8, x_12);
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = 1;
x_16 = lean_usize_add(x_6, x_15);
x_17 = lean_unbox(x_14);
lean_dec(x_14);
x_6 = x_16;
x_8 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec_ref(x_9);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_19 = lean_box(x_8);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
static lean_object* _init_l_Lake_CacheService_downloadArtifacts___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": failed to download some artifacts", 35, 35);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_1);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_dec(x_13);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_8 = lean_box(0);
goto block_11;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_13, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_8 = lean_box(0);
goto block_11;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; uint8_t x_19; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_13);
lean_dec(x_13);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__0(x_2, x_3, x_4, x_5, x_1, x_16, x_17, x_15, x_6);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = l_Lake_CacheService_downloadArtifacts___closed__0;
x_23 = lean_string_append(x_4, x_22);
x_24 = 3;
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
x_26 = lean_apply_2(x_6, x_25, lean_box(0));
x_27 = lean_box(0);
lean_ctor_set_tag(x_18, 1);
lean_ctor_set(x_18, 0, x_27);
return x_18;
}
else
{
lean_free_object(x_18);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
x_8 = lean_box(0);
goto block_11;
}
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_18, 0);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = l_Lake_CacheService_downloadArtifacts___closed__0;
x_31 = lean_string_append(x_4, x_30);
x_32 = 3;
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
x_34 = lean_apply_2(x_6, x_33, lean_box(0));
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
else
{
lean_dec_ref(x_6);
lean_dec_ref(x_4);
x_8 = lean_box(0);
goto block_11;
}
}
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact___at___00Lake_CacheService_downloadArtifacts___elam__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_6);
x_9 = l_Lake_CacheService_downloadArtifact___at___00Lake_CacheService_downloadArtifacts___elam__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_8);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___elam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_4);
x_10 = lean_unbox(x_5);
x_11 = l_Lake_CacheService_downloadArtifacts___elam__0(x_1, x_2, x_3, x_9, x_10, x_6, x_7);
lean_dec_ref(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_5);
x_10 = lean_unbox(x_6);
x_11 = l_Lake_CacheService_downloadArtifacts___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__0_spec__0(x_1, x_2, x_3, x_4, x_9, x_10, x_7);
lean_dec_ref(x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; uint8_t x_14; lean_object* x_15; 
x_11 = lean_unbox(x_4);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_14 = lean_unbox(x_8);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__0(x_1, x_2, x_3, x_11, x_5, x_12, x_13, x_14, x_9);
lean_dec_ref(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
x_9 = l_Lake_CacheService_downloadArtifacts(x_1, x_2, x_3, x_4, x_8, x_6);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
lean_object* x_8; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_2);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_dec(x_13);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_8 = lean_box(0);
goto block_11;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_13, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_8 = lean_box(0);
goto block_11;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; uint8_t x_19; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_13);
lean_dec(x_13);
lean_inc_ref(x_1);
lean_inc_ref(x_5);
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__0(x_3, x_4, x_5, x_6, x_2, x_16, x_17, x_15, x_1);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = l_Lake_CacheService_downloadArtifacts___closed__0;
x_23 = lean_string_append(x_5, x_22);
x_24 = 3;
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
x_26 = lean_apply_2(x_1, x_25, lean_box(0));
x_27 = lean_box(0);
lean_ctor_set_tag(x_18, 1);
lean_ctor_set(x_18, 0, x_27);
return x_18;
}
else
{
lean_free_object(x_18);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_8 = lean_box(0);
goto block_11;
}
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_18, 0);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = l_Lake_CacheService_downloadArtifacts___closed__0;
x_31 = lean_string_append(x_5, x_30);
x_32 = 3;
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
x_34 = lean_apply_2(x_1, x_33, lean_box(0));
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
else
{
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_8 = lean_box(0);
goto block_11;
}
}
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadOutputArtifacts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_13; 
lean_inc_ref(x_2);
x_13 = l_Lake_Cache_writeMap(x_2, x_4, x_1);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lake_CacheMap_parse___closed__5;
x_18 = l_Lake_CacheMap_collectOutputDescrs(x_1, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_free_object(x_13);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_array_get_size(x_20);
x_22 = lean_nat_dec_lt(x_16, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_21);
lean_dec(x_20);
x_23 = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(x_7, x_19, x_2, x_3, x_5, x_6);
lean_dec(x_19);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_21, x_21);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_21);
lean_dec(x_20);
x_25 = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(x_7, x_19, x_2, x_3, x_5, x_6);
lean_dec(x_19);
return x_25;
}
else
{
lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_box(0);
x_27 = 0;
x_28 = lean_usize_of_nat(x_21);
lean_dec(x_21);
lean_inc_ref(x_7);
x_29 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(x_20, x_27, x_28, x_26, x_7);
lean_dec(x_20);
lean_dec_ref(x_29);
x_30 = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(x_7, x_19, x_2, x_3, x_5, x_6);
lean_dec(x_19);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_31 = lean_ctor_get(x_18, 1);
lean_inc(x_31);
lean_dec_ref(x_18);
x_32 = lean_array_get_size(x_31);
x_33 = lean_nat_dec_lt(x_16, x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec_ref(x_7);
x_34 = lean_box(0);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_34);
return x_13;
}
else
{
uint8_t x_35; 
lean_free_object(x_13);
x_35 = lean_nat_dec_le(x_32, x_32);
if (x_35 == 0)
{
lean_dec(x_32);
lean_dec(x_31);
lean_dec_ref(x_7);
x_9 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; 
x_36 = lean_box(0);
x_37 = 0;
x_38 = lean_usize_of_nat(x_32);
lean_dec(x_32);
x_39 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(x_31, x_37, x_38, x_36, x_7);
lean_dec(x_31);
lean_dec_ref(x_39);
x_9 = lean_box(0);
goto block_12;
}
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_13);
x_40 = lean_unsigned_to_nat(0u);
x_41 = l_Lake_CacheMap_parse___closed__5;
x_42 = l_Lake_CacheMap_collectOutputDescrs(x_1, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
x_45 = lean_array_get_size(x_44);
x_46 = lean_nat_dec_lt(x_40, x_45);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_45);
lean_dec(x_44);
x_47 = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(x_7, x_43, x_2, x_3, x_5, x_6);
lean_dec(x_43);
return x_47;
}
else
{
uint8_t x_48; 
x_48 = lean_nat_dec_le(x_45, x_45);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_45);
lean_dec(x_44);
x_49 = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(x_7, x_43, x_2, x_3, x_5, x_6);
lean_dec(x_43);
return x_49;
}
else
{
lean_object* x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_box(0);
x_51 = 0;
x_52 = lean_usize_of_nat(x_45);
lean_dec(x_45);
lean_inc_ref(x_7);
x_53 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(x_44, x_51, x_52, x_50, x_7);
lean_dec(x_44);
lean_dec_ref(x_53);
x_54 = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(x_7, x_43, x_2, x_3, x_5, x_6);
lean_dec(x_43);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_55 = lean_ctor_get(x_42, 1);
lean_inc(x_55);
lean_dec_ref(x_42);
x_56 = lean_array_get_size(x_55);
x_57 = lean_nat_dec_lt(x_40, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_7);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
else
{
uint8_t x_60; 
x_60 = lean_nat_dec_le(x_56, x_56);
if (x_60 == 0)
{
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_7);
x_9 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_61; size_t x_62; size_t x_63; lean_object* x_64; 
x_61 = lean_box(0);
x_62 = 0;
x_63 = lean_usize_of_nat(x_56);
lean_dec(x_56);
x_64 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(x_55, x_62, x_63, x_61, x_7);
lean_dec(x_55);
lean_dec_ref(x_64);
x_9 = lean_box(0);
goto block_12;
}
}
}
}
}
else
{
uint8_t x_65; 
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_65 = !lean_is_exclusive(x_13);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = lean_ctor_get(x_13, 0);
x_67 = lean_io_error_to_string(x_66);
x_68 = 3;
x_69 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set_uint8(x_69, sizeof(void*)*1, x_68);
x_70 = lean_apply_2(x_7, x_69, lean_box(0));
x_71 = lean_box(0);
lean_ctor_set(x_13, 0, x_71);
return x_13;
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_72 = lean_ctor_get(x_13, 0);
lean_inc(x_72);
lean_dec(x_13);
x_73 = lean_io_error_to_string(x_72);
x_74 = 3;
x_75 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set_uint8(x_75, sizeof(void*)*1, x_74);
x_76 = lean_apply_2(x_7, x_75, lean_box(0));
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_6);
x_9 = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(x_1, x_2, x_3, x_4, x_5, x_8);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadOutputArtifacts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_6);
x_10 = l_Lake_CacheService_downloadOutputArtifacts(x_1, x_2, x_3, x_4, x_5, x_9, x_7);
lean_dec_ref(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_11 = l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__0;
x_12 = l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__1;
x_13 = l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6;
x_14 = l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__7;
x_15 = l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__8;
x_16 = l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9;
x_17 = l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10;
x_18 = lean_string_append(x_17, x_3);
x_19 = l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__15;
x_20 = lean_array_push(x_19, x_5);
x_21 = lean_array_push(x_20, x_13);
x_22 = lean_array_push(x_21, x_14);
x_23 = lean_array_push(x_22, x_15);
x_24 = lean_array_push(x_23, x_2);
x_25 = lean_array_push(x_24, x_4);
x_26 = lean_array_push(x_25, x_16);
x_27 = lean_array_push(x_26, x_18);
x_28 = lean_box(0);
x_29 = lean_unsigned_to_nat(0u);
x_30 = l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16;
x_31 = 1;
x_32 = 0;
x_33 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_33, 0, x_11);
lean_ctor_set(x_33, 1, x_12);
lean_ctor_set(x_33, 2, x_27);
lean_ctor_set(x_33, 3, x_28);
lean_ctor_set(x_33, 4, x_30);
lean_ctor_set_uint8(x_33, sizeof(void*)*5, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*5 + 1, x_32);
x_34 = l_Lake_proc(x_33, x_31, x_30);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec_ref(x_34);
x_37 = lean_array_get_size(x_36);
x_38 = lean_nat_dec_lt(x_29, x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec_ref(x_1);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_35);
return x_39;
}
else
{
uint8_t x_40; 
x_40 = lean_nat_dec_le(x_37, x_37);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec_ref(x_1);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_35);
return x_41;
}
else
{
lean_object* x_42; size_t x_43; size_t x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_box(0);
x_43 = 0;
x_44 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_45 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(x_36, x_43, x_44, x_42, x_1);
lean_dec(x_36);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set(x_45, 0, x_35);
return x_45;
}
else
{
lean_object* x_48; 
lean_dec(x_45);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_35);
return x_48;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_34, 1);
lean_inc(x_49);
lean_dec_ref(x_34);
x_50 = lean_array_get_size(x_49);
x_51 = lean_nat_dec_lt(x_29, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec_ref(x_1);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
else
{
uint8_t x_54; 
x_54 = lean_nat_dec_le(x_50, x_50);
if (x_54 == 0)
{
lean_dec(x_50);
lean_dec(x_49);
lean_dec_ref(x_1);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_55; size_t x_56; size_t x_57; lean_object* x_58; 
x_55 = lean_box(0);
x_56 = 0;
x_57 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_58 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(x_49, x_56, x_57, x_55, x_1);
lean_dec(x_49);
lean_dec_ref(x_58);
x_7 = lean_box(0);
goto block_10;
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
static lean_object* _init_l_Lake_CacheService_uploadArtifact___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": uploading artifact ", 21, 21);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact(uint64_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_inc_ref(x_3);
x_7 = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(x_1, x_3, x_4);
x_8 = l_Lake_CacheService_uploadArtifact___closed__0;
x_9 = lean_string_append(x_4, x_8);
x_10 = l_Lake_Hash_hex(x_1);
x_11 = lean_string_append(x_9, x_10);
lean_dec_ref(x_10);
x_12 = l_Lake_CacheService_downloadArtifact___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_string_append(x_13, x_2);
x_15 = l_Lake_CacheService_downloadArtifact___closed__3;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_string_append(x_16, x_7);
x_18 = 1;
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
lean_inc_ref(x_5);
x_20 = lean_apply_2(x_5, x_19, lean_box(0));
x_21 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_21);
lean_dec_ref(x_3);
x_22 = l_Lake_CacheService_artifactContentType___closed__0;
x_23 = l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(x_5, x_2, x_22, x_7, x_21);
return x_23;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint64_t x_7; lean_object* x_8; 
x_7 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_8 = l_Lake_CacheService_uploadArtifact(x_7, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact___at___00Lake_CacheService_uploadArtifacts___elam__0_spec__0(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_inc_ref(x_4);
x_7 = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(x_2, x_4, x_5);
x_8 = l_Lake_CacheService_uploadArtifact___closed__0;
x_9 = lean_string_append(x_5, x_8);
x_10 = l_Lake_Hash_hex(x_2);
x_11 = lean_string_append(x_9, x_10);
lean_dec_ref(x_10);
x_12 = l_Lake_CacheService_downloadArtifact___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_string_append(x_13, x_3);
x_15 = l_Lake_CacheService_downloadArtifact___closed__3;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_string_append(x_16, x_7);
x_18 = 1;
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
lean_inc_ref(x_1);
x_20 = lean_apply_2(x_1, x_19, lean_box(0));
x_21 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_21);
lean_dec_ref(x_4);
x_22 = l_Lake_CacheService_artifactContentType___closed__0;
x_23 = l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(x_1, x_3, x_22, x_7, x_21);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; uint64_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_fget_borrowed(x_1, x_5);
x_9 = lean_ctor_get_uint64(x_8, sizeof(void*)*1);
x_10 = lean_array_fget_borrowed(x_2, x_5);
lean_inc_ref(x_10);
x_11 = l_Lake_CacheService_uploadArtifact___at___00Lake_CacheService_uploadArtifacts___elam__0_spec__0(x_6, x_9, x_10, x_3, x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_CacheService_uploadArtifacts___elam__0___redArg(x_1, x_2, x_3, x_4, x_5, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; uint64_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_fget_borrowed(x_2, x_6);
x_9 = lean_ctor_get_uint64(x_8, sizeof(void*)*1);
x_10 = lean_array_fget_borrowed(x_3, x_6);
lean_inc_ref(x_10);
x_11 = l_Lake_CacheService_uploadArtifact___at___00Lake_CacheService_uploadArtifacts___elam__0_spec__0(x_1, x_9, x_10, x_4, x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_6, x_9);
if (x_10 == 1)
{
lean_object* x_11; lean_object* x_12; 
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_6, x_13);
lean_dec(x_6);
x_15 = lean_nat_sub(x_5, x_14);
x_16 = lean_nat_sub(x_15, x_13);
lean_dec(x_15);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_7);
x_17 = l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0_spec__0___redArg(x_7, x_1, x_2, x_3, x_4, x_16);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_dec_ref(x_17);
x_6 = x_14;
goto _start;
}
else
{
lean_dec(x_14);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg(x_2, x_3, x_4, x_5, x_1, x_1, x_6);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact___at___00Lake_CacheService_uploadArtifacts___elam__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint64_t x_7; lean_object* x_8; 
x_7 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_8 = l_Lake_CacheService_uploadArtifact___at___00Lake_CacheService_uploadArtifacts___elam__0_spec__0(x_1, x_7, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_CacheService_uploadArtifacts___elam__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_CacheService_uploadArtifacts___elam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_CacheService_uploadArtifacts___elam__0___at___00__private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_CacheService_uploadArtifacts(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
static lean_object* _init_l_Lake_CacheService_mapContentType___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("application/vnd.reservoir.outputs+json-lines", 44, 44);
return x_1;
}
}
static lean_object* _init_l_Lake_CacheService_mapContentType() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_CacheService_mapContentType___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_string_append(x_2, x_1);
x_5 = l_Lake_Cache_revisionPath___closed__0;
x_6 = lean_string_append(x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tc/", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("pt/", 3, 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_6 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_6);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 1);
lean_dec_ref(x_2);
x_24 = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0;
x_25 = lean_string_append(x_6, x_24);
x_26 = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(x_25, x_3);
if (x_7 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_box(0);
x_28 = l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___lam__0(x_1, x_26, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_string_utf8_byte_size(x_4);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_nat_dec_eq(x_29, x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint32_t x_35; lean_object* x_36; 
x_32 = l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__1;
x_33 = lean_string_append(x_26, x_32);
x_34 = l_Lake_uriEncode(x_4, x_33);
x_35 = 47;
x_36 = lean_string_push(x_34, x_35);
x_8 = x_36;
goto block_23;
}
else
{
x_8 = x_26;
goto block_23;
}
}
block_23:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_string_utf8_byte_size(x_5);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint32_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = l_Lake_CacheService_reservoirService___closed__0;
x_13 = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(x_5, x_12, x_10);
x_14 = l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__0;
x_15 = lean_string_append(x_8, x_14);
x_16 = l_Lake_uriEncode(x_13, x_15);
lean_dec_ref(x_13);
x_17 = 47;
x_18 = lean_string_push(x_16, x_17);
x_19 = lean_box(0);
x_20 = l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___lam__0(x_1, x_18, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___lam__0(x_1, x_8, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_6;
}
}
static lean_object* _init_l_Lake_CacheService_revisionUrl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("&toolchain=", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_CacheService_revisionUrl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("build-outputs\?rev=", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lake_CacheService_revisionUrl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("&platform=", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_revisionUrl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_14; uint8_t x_26; 
x_26 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(x_1, x_2, x_3, x_4, x_5);
return x_27;
}
else
{
uint8_t x_28; 
x_28 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 1);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_29);
lean_dec_ref(x_2);
x_30 = l_Lake_CacheService_artifactUrl___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_14 = x_31;
goto block_25;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_32);
lean_dec_ref(x_2);
x_33 = l_Lake_CacheService_artifactUrl___closed__2;
x_34 = lean_string_append(x_32, x_33);
x_14 = x_34;
goto block_25;
}
}
block_13:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_string_utf8_byte_size(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lake_CacheService_revisionUrl___closed__0;
x_11 = lean_string_append(x_6, x_10);
x_12 = l_Lake_uriEncode(x_5, x_11);
return x_12;
}
else
{
return x_6;
}
}
block_25:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(x_14, x_3);
x_16 = l_Lake_CacheService_revisionUrl___closed__1;
x_17 = lean_string_append(x_16, x_1);
x_18 = lean_string_append(x_15, x_17);
lean_dec_ref(x_17);
x_19 = lean_string_utf8_byte_size(x_4);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_19, x_20);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = l_Lake_CacheService_revisionUrl___closed__2;
x_23 = lean_string_append(x_18, x_22);
x_24 = l_Lake_uriEncode(x_4, x_23);
x_6 = x_24;
goto block_13;
}
else
{
x_6 = x_18;
goto block_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_revisionUrl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_CacheService_revisionUrl(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_6;
}
}
static lean_object* _init_l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": output lookup failed", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": downloading build outputs for revision ", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Reservoir_lakeHeaders;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_20; lean_object* x_24; lean_object* x_25; lean_object* x_29; lean_object* x_30; lean_object* x_38; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_153; uint8_t x_171; lean_object* x_172; lean_object* x_196; uint8_t x_197; 
x_41 = l_Lake_Cache_revisionDir___closed__0;
x_42 = l_System_FilePath_join(x_2, x_41);
x_43 = l_System_FilePath_join(x_42, x_4);
x_44 = l_Lake_Cache_revisionPath___closed__0;
lean_inc_ref(x_1);
x_45 = lean_string_append(x_1, x_44);
x_46 = l_System_FilePath_join(x_43, x_45);
lean_dec_ref(x_45);
x_171 = l_System_FilePath_pathExists(x_46);
x_196 = l_Lake_CacheMap_parse___closed__5;
x_197 = l_Lake_CacheService_downloadArtifact___closed__5;
if (x_197 == 0)
{
x_172 = lean_box(0);
goto block_195;
}
else
{
uint8_t x_198; 
x_198 = l_Lake_CacheService_downloadArtifact___closed__6;
if (x_198 == 0)
{
x_172 = lean_box(0);
goto block_195;
}
else
{
lean_object* x_199; size_t x_200; size_t x_201; lean_object* x_202; 
x_199 = lean_box(0);
x_200 = 0;
x_201 = l_Lake_CacheService_downloadArtifact___closed__7;
lean_inc_ref(x_9);
x_202 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(x_196, x_200, x_201, x_199, x_9);
lean_dec_ref(x_202);
x_172 = lean_box(0);
goto block_195;
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
block_19:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_15);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
block_23:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
block_28:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_24);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
block_37:
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__0;
x_32 = lean_string_append(x_5, x_31);
x_33 = 3;
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_33);
x_35 = lean_apply_2(x_9, x_34, lean_box(0));
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_29);
return x_36;
}
block_40:
{
lean_object* x_39; 
x_39 = lean_box(0);
x_29 = x_39;
x_30 = lean_box(0);
goto block_37;
}
block_127:
{
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec_ref(x_46);
lean_dec_ref(x_9);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_47, 0);
lean_inc(x_51);
lean_dec_ref(x_47);
x_52 = l_Lake_createParentDirs(x_46);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
lean_dec_ref(x_52);
x_53 = l_IO_FS_writeFile(x_46, x_51);
lean_dec(x_51);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
x_56 = lean_unsigned_to_nat(0u);
x_57 = l_Lake_CacheMap_parse___closed__5;
x_58 = l_Lake_CacheMap_load(x_46, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_free_object(x_53);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec_ref(x_58);
x_61 = lean_array_get_size(x_60);
x_62 = lean_nat_dec_lt(x_56, x_61);
if (x_62 == 0)
{
lean_dec(x_61);
lean_dec(x_60);
lean_dec_ref(x_9);
x_24 = x_59;
x_25 = lean_box(0);
goto block_28;
}
else
{
uint8_t x_63; 
x_63 = lean_nat_dec_le(x_61, x_61);
if (x_63 == 0)
{
lean_dec(x_61);
lean_dec(x_60);
lean_dec_ref(x_9);
x_24 = x_59;
x_25 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_64; size_t x_65; size_t x_66; lean_object* x_67; 
x_64 = lean_box(0);
x_65 = 0;
x_66 = lean_usize_of_nat(x_61);
lean_dec(x_61);
x_67 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(x_60, x_65, x_66, x_64, x_9);
lean_dec(x_60);
lean_dec_ref(x_67);
x_24 = x_59;
x_25 = lean_box(0);
goto block_28;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_58, 1);
lean_inc(x_68);
lean_dec_ref(x_58);
x_69 = lean_array_get_size(x_68);
x_70 = lean_nat_dec_lt(x_56, x_69);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_69);
lean_dec(x_68);
lean_dec_ref(x_9);
x_71 = lean_box(0);
lean_ctor_set_tag(x_53, 1);
lean_ctor_set(x_53, 0, x_71);
return x_53;
}
else
{
uint8_t x_72; 
lean_free_object(x_53);
x_72 = lean_nat_dec_le(x_69, x_69);
if (x_72 == 0)
{
lean_dec(x_69);
lean_dec(x_68);
lean_dec_ref(x_9);
x_20 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_73; size_t x_74; size_t x_75; lean_object* x_76; 
x_73 = lean_box(0);
x_74 = 0;
x_75 = lean_usize_of_nat(x_69);
lean_dec(x_69);
x_76 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(x_68, x_74, x_75, x_73, x_9);
lean_dec(x_68);
lean_dec_ref(x_76);
x_20 = lean_box(0);
goto block_23;
}
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_53);
x_77 = lean_unsigned_to_nat(0u);
x_78 = l_Lake_CacheMap_parse___closed__5;
x_79 = l_Lake_CacheMap_load(x_46, x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec_ref(x_79);
x_82 = lean_array_get_size(x_81);
x_83 = lean_nat_dec_lt(x_77, x_82);
if (x_83 == 0)
{
lean_dec(x_82);
lean_dec(x_81);
lean_dec_ref(x_9);
x_24 = x_80;
x_25 = lean_box(0);
goto block_28;
}
else
{
uint8_t x_84; 
x_84 = lean_nat_dec_le(x_82, x_82);
if (x_84 == 0)
{
lean_dec(x_82);
lean_dec(x_81);
lean_dec_ref(x_9);
x_24 = x_80;
x_25 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_85; size_t x_86; size_t x_87; lean_object* x_88; 
x_85 = lean_box(0);
x_86 = 0;
x_87 = lean_usize_of_nat(x_82);
lean_dec(x_82);
x_88 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(x_81, x_86, x_87, x_85, x_9);
lean_dec(x_81);
lean_dec_ref(x_88);
x_24 = x_80;
x_25 = lean_box(0);
goto block_28;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_89 = lean_ctor_get(x_79, 1);
lean_inc(x_89);
lean_dec_ref(x_79);
x_90 = lean_array_get_size(x_89);
x_91 = lean_nat_dec_lt(x_77, x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_90);
lean_dec(x_89);
lean_dec_ref(x_9);
x_92 = lean_box(0);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
else
{
uint8_t x_94; 
x_94 = lean_nat_dec_le(x_90, x_90);
if (x_94 == 0)
{
lean_dec(x_90);
lean_dec(x_89);
lean_dec_ref(x_9);
x_20 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_95; size_t x_96; size_t x_97; lean_object* x_98; 
x_95 = lean_box(0);
x_96 = 0;
x_97 = lean_usize_of_nat(x_90);
lean_dec(x_90);
x_98 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(x_89, x_96, x_97, x_95, x_9);
lean_dec(x_89);
lean_dec_ref(x_98);
x_20 = lean_box(0);
goto block_23;
}
}
}
}
}
else
{
uint8_t x_99; 
lean_dec_ref(x_46);
x_99 = !lean_is_exclusive(x_53);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_100 = lean_ctor_get(x_53, 0);
x_101 = lean_io_error_to_string(x_100);
x_102 = 3;
x_103 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set_uint8(x_103, sizeof(void*)*1, x_102);
x_104 = lean_apply_2(x_9, x_103, lean_box(0));
x_105 = lean_box(0);
lean_ctor_set(x_53, 0, x_105);
return x_53;
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_106 = lean_ctor_get(x_53, 0);
lean_inc(x_106);
lean_dec(x_53);
x_107 = lean_io_error_to_string(x_106);
x_108 = 3;
x_109 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set_uint8(x_109, sizeof(void*)*1, x_108);
x_110 = lean_apply_2(x_9, x_109, lean_box(0));
x_111 = lean_box(0);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_51);
lean_dec_ref(x_46);
x_113 = !lean_is_exclusive(x_52);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_114 = lean_ctor_get(x_52, 0);
x_115 = lean_io_error_to_string(x_114);
x_116 = 3;
x_117 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set_uint8(x_117, sizeof(void*)*1, x_116);
x_118 = lean_apply_2(x_9, x_117, lean_box(0));
x_119 = lean_box(0);
lean_ctor_set(x_52, 0, x_119);
return x_52;
}
else
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_120 = lean_ctor_get(x_52, 0);
lean_inc(x_120);
lean_dec(x_52);
x_121 = lean_io_error_to_string(x_120);
x_122 = 3;
x_123 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set_uint8(x_123, sizeof(void*)*1, x_122);
x_124 = lean_apply_2(x_9, x_123, lean_box(0));
x_125 = lean_box(0);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
}
}
}
block_152:
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_unsigned_to_nat(0u);
x_132 = l_Lake_CacheMap_parse___closed__5;
x_133 = l_Lake_getUrl_x3f(x_129, x_130, x_132);
lean_dec_ref(x_130);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
lean_dec_ref(x_5);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec_ref(x_133);
x_136 = lean_array_get_size(x_135);
x_137 = lean_nat_dec_lt(x_131, x_136);
if (x_137 == 0)
{
lean_dec(x_136);
lean_dec(x_135);
x_47 = x_134;
x_48 = lean_box(0);
goto block_127;
}
else
{
uint8_t x_138; 
x_138 = lean_nat_dec_le(x_136, x_136);
if (x_138 == 0)
{
lean_dec(x_136);
lean_dec(x_135);
x_47 = x_134;
x_48 = lean_box(0);
goto block_127;
}
else
{
lean_object* x_139; size_t x_140; size_t x_141; lean_object* x_142; 
x_139 = lean_box(0);
x_140 = 0;
x_141 = lean_usize_of_nat(x_136);
lean_dec(x_136);
lean_inc_ref(x_9);
x_142 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(x_135, x_140, x_141, x_139, x_9);
lean_dec(x_135);
lean_dec_ref(x_142);
x_47 = x_134;
x_48 = lean_box(0);
goto block_127;
}
}
}
else
{
lean_object* x_143; lean_object* x_144; uint8_t x_145; 
lean_dec_ref(x_46);
x_143 = lean_ctor_get(x_133, 1);
lean_inc(x_143);
lean_dec_ref(x_133);
x_144 = lean_array_get_size(x_143);
x_145 = lean_nat_dec_lt(x_131, x_144);
if (x_145 == 0)
{
lean_object* x_146; 
lean_dec(x_144);
lean_dec(x_143);
x_146 = lean_box(0);
x_29 = x_146;
x_30 = lean_box(0);
goto block_37;
}
else
{
uint8_t x_147; 
x_147 = lean_nat_dec_le(x_144, x_144);
if (x_147 == 0)
{
lean_dec(x_144);
lean_dec(x_143);
x_38 = lean_box(0);
goto block_40;
}
else
{
lean_object* x_148; size_t x_149; size_t x_150; lean_object* x_151; 
x_148 = lean_box(0);
x_149 = 0;
x_150 = lean_usize_of_nat(x_144);
lean_dec(x_144);
lean_inc_ref(x_9);
x_151 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(x_143, x_149, x_150, x_148, x_9);
lean_dec(x_143);
lean_dec_ref(x_151);
x_38 = lean_box(0);
goto block_40;
}
}
}
}
block_170:
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
lean_inc_ref(x_3);
x_154 = l_Lake_CacheService_revisionUrl(x_1, x_3, x_5, x_6, x_7);
x_155 = l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__1;
x_156 = lean_string_append(x_4, x_155);
x_157 = lean_string_append(x_156, x_1);
lean_dec_ref(x_1);
x_158 = l_Lake_CacheService_downloadArtifact___closed__2;
x_159 = lean_string_append(x_157, x_158);
x_160 = lean_string_append(x_159, x_46);
x_161 = l_Lake_CacheService_downloadArtifact___closed__3;
x_162 = lean_string_append(x_160, x_161);
x_163 = lean_string_append(x_162, x_154);
x_164 = 1;
x_165 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set_uint8(x_165, sizeof(void*)*1, x_164);
lean_inc_ref(x_9);
x_166 = lean_apply_2(x_9, x_165, lean_box(0));
x_167 = lean_ctor_get_uint8(x_3, sizeof(void*)*4);
lean_dec_ref(x_3);
if (x_167 == 0)
{
lean_object* x_168; 
x_168 = l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__2;
x_128 = lean_box(0);
x_129 = x_154;
x_130 = x_168;
goto block_152;
}
else
{
lean_object* x_169; 
x_169 = l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__3;
x_128 = lean_box(0);
x_129 = x_154;
x_130 = x_169;
goto block_152;
}
}
block_195:
{
if (x_171 == 0)
{
x_153 = lean_box(0);
goto block_170;
}
else
{
if (x_8 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_173 = lean_unsigned_to_nat(0u);
x_174 = l_Lake_CacheMap_parse___closed__5;
x_175 = l_Lake_CacheMap_load(x_46, x_174);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec_ref(x_175);
x_178 = lean_array_get_size(x_177);
x_179 = lean_nat_dec_lt(x_173, x_178);
if (x_179 == 0)
{
lean_dec(x_178);
lean_dec(x_177);
lean_dec_ref(x_9);
x_15 = x_176;
x_16 = lean_box(0);
goto block_19;
}
else
{
uint8_t x_180; 
x_180 = lean_nat_dec_le(x_178, x_178);
if (x_180 == 0)
{
lean_dec(x_178);
lean_dec(x_177);
lean_dec_ref(x_9);
x_15 = x_176;
x_16 = lean_box(0);
goto block_19;
}
else
{
lean_object* x_181; size_t x_182; size_t x_183; lean_object* x_184; 
x_181 = lean_box(0);
x_182 = 0;
x_183 = lean_usize_of_nat(x_178);
lean_dec(x_178);
x_184 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(x_177, x_182, x_183, x_181, x_9);
lean_dec(x_177);
lean_dec_ref(x_184);
x_15 = x_176;
x_16 = lean_box(0);
goto block_19;
}
}
}
else
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_185 = lean_ctor_get(x_175, 1);
lean_inc(x_185);
lean_dec_ref(x_175);
x_186 = lean_array_get_size(x_185);
x_187 = lean_nat_dec_lt(x_173, x_186);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; 
lean_dec(x_186);
lean_dec(x_185);
lean_dec_ref(x_9);
x_188 = lean_box(0);
x_189 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_189, 0, x_188);
return x_189;
}
else
{
uint8_t x_190; 
x_190 = lean_nat_dec_le(x_186, x_186);
if (x_190 == 0)
{
lean_dec(x_186);
lean_dec(x_185);
lean_dec_ref(x_9);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_191; size_t x_192; size_t x_193; lean_object* x_194; 
x_191 = lean_box(0);
x_192 = 0;
x_193 = lean_usize_of_nat(x_186);
lean_dec(x_186);
x_194 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(x_185, x_192, x_193, x_191, x_9);
lean_dec(x_185);
lean_dec_ref(x_194);
x_11 = lean_box(0);
goto block_14;
}
}
}
}
else
{
x_153 = lean_box(0);
goto block_170;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_8);
x_12 = l_Lake_CacheService_downloadRevisionOutputs_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11, x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
return x_12;
}
}
static lean_object* _init_l_Lake_CacheService_uploadRevisionOutputs___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": uploading build outputs for revision ", 39, 39);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadRevisionOutputs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_inc_ref(x_3);
x_9 = l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(x_1, x_3, x_4, x_5, x_6);
x_10 = l_Lake_CacheService_uploadRevisionOutputs___closed__0;
x_11 = lean_string_append(x_4, x_10);
x_12 = lean_string_append(x_11, x_1);
x_13 = l_Lake_CacheService_downloadArtifact___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_string_append(x_14, x_2);
x_16 = l_Lake_CacheService_downloadArtifact___closed__3;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_string_append(x_17, x_9);
x_19 = 1;
x_20 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_19);
lean_inc_ref(x_7);
x_21 = lean_apply_2(x_7, x_20, lean_box(0));
x_22 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_22);
lean_dec_ref(x_3);
x_23 = l_Lake_CacheService_mapContentType___closed__0;
x_24 = l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(x_7, x_2, x_23, x_9, x_22);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadRevisionOutputs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_CacheService_uploadRevisionOutputs(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
lean_object* initialize_Lake_Util_Log(uint8_t builtin);
lean_object* initialize_Lake_Config_Artifact(uint8_t builtin);
lean_object* initialize_Lake_Config_InstallPath(uint8_t builtin);
lean_object* initialize_Lake_Build_Actions(uint8_t builtin);
lean_object* initialize_Lake_Util_Url(uint8_t builtin);
lean_object* initialize_Lake_Util_Proc(uint8_t builtin);
lean_object* initialize_Lake_Util_Reservoir(uint8_t builtin);
lean_object* initialize_Lake_Util_IO(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Cache(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Log(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Artifact(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_InstallPath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Url(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Proc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Reservoir(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_CacheMap_schemaVersion___closed__0 = _init_l_Lake_CacheMap_schemaVersion___closed__0();
lean_mark_persistent(l_Lake_CacheMap_schemaVersion___closed__0);
l_Lake_CacheMap_schemaVersion = _init_l_Lake_CacheMap_schemaVersion();
lean_mark_persistent(l_Lake_CacheMap_schemaVersion);
l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__0 = _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__0();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__0);
l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__1 = _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__1();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__1);
l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__2 = _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__2();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__2);
l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__3 = _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__3();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__3);
l_Prod_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__8___closed__0 = _init_l_Prod_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__8___closed__0();
lean_mark_persistent(l_Prod_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__8___closed__0);
l_Prod_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__8___closed__1 = _init_l_Prod_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__8___closed__1();
lean_mark_persistent(l_Prod_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__8___closed__1);
l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__0 = _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__0();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__0);
l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__1 = _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__1();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__1);
l_Lake_CacheMap_parse___closed__0 = _init_l_Lake_CacheMap_parse___closed__0();
lean_mark_persistent(l_Lake_CacheMap_parse___closed__0);
l_Lake_CacheMap_parse___closed__1 = _init_l_Lake_CacheMap_parse___closed__1();
lean_mark_persistent(l_Lake_CacheMap_parse___closed__1);
l_Lake_CacheMap_parse___closed__2 = _init_l_Lake_CacheMap_parse___closed__2();
lean_mark_persistent(l_Lake_CacheMap_parse___closed__2);
l_Lake_CacheMap_parse___closed__3 = _init_l_Lake_CacheMap_parse___closed__3();
lean_mark_persistent(l_Lake_CacheMap_parse___closed__3);
l_Lake_CacheMap_parse___closed__4 = _init_l_Lake_CacheMap_parse___closed__4();
lean_mark_persistent(l_Lake_CacheMap_parse___closed__4);
l_Lake_CacheMap_parse___closed__5 = _init_l_Lake_CacheMap_parse___closed__5();
lean_mark_persistent(l_Lake_CacheMap_parse___closed__5);
l_Lake_CacheMap_load___closed__0 = _init_l_Lake_CacheMap_load___closed__0();
lean_mark_persistent(l_Lake_CacheMap_load___closed__0);
l_Prod_toJson___at___00Lake_CacheMap_updateFile_spec__0___closed__0 = _init_l_Prod_toJson___at___00Lake_CacheMap_updateFile_spec__0___closed__0();
lean_mark_persistent(l_Prod_toJson___at___00Lake_CacheMap_updateFile_spec__0___closed__0);
l_Lake_CacheMap_updateFile___closed__0 = _init_l_Lake_CacheMap_updateFile___closed__0();
lean_mark_persistent(l_Lake_CacheMap_updateFile___closed__0);
l_Lake_CacheMap_updateFile___closed__1 = _init_l_Lake_CacheMap_updateFile___closed__1();
lean_mark_persistent(l_Lake_CacheMap_updateFile___closed__1);
l_Lake_CacheMap_writeFile___closed__0 = _init_l_Lake_CacheMap_writeFile___closed__0();
lean_mark_persistent(l_Lake_CacheMap_writeFile___closed__0);
l_Lake_CacheMap_writeFile___closed__1 = _init_l_Lake_CacheMap_writeFile___closed__1();
lean_mark_persistent(l_Lake_CacheMap_writeFile___closed__1);
l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__0 = _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__0();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__0);
l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__1 = _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__1();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__1);
l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__2 = _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__2();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__2);
l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__3 = _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__3();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__3);
l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__4 = _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__4();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__4);
l_Lake_CacheMap_collectOutputDescrs___closed__0 = _init_l_Lake_CacheMap_collectOutputDescrs___closed__0();
lean_mark_persistent(l_Lake_CacheMap_collectOutputDescrs___closed__0);
l_Lake_instInhabitedCache_default___closed__0 = _init_l_Lake_instInhabitedCache_default___closed__0();
lean_mark_persistent(l_Lake_instInhabitedCache_default___closed__0);
l_Lake_instInhabitedCache_default = _init_l_Lake_instInhabitedCache_default();
lean_mark_persistent(l_Lake_instInhabitedCache_default);
l_Lake_instInhabitedCache = _init_l_Lake_instInhabitedCache();
lean_mark_persistent(l_Lake_instInhabitedCache);
l_Lake_Cache_artifactDir___closed__0 = _init_l_Lake_Cache_artifactDir___closed__0();
lean_mark_persistent(l_Lake_Cache_artifactDir___closed__0);
l_Lake_Cache_artifactPath___closed__0 = _init_l_Lake_Cache_artifactPath___closed__0();
lean_mark_persistent(l_Lake_Cache_artifactPath___closed__0);
l_Lake_Cache_getArtifact_x3f___closed__0 = _init_l_Lake_Cache_getArtifact_x3f___closed__0();
lean_mark_persistent(l_Lake_Cache_getArtifact_x3f___closed__0);
l_Lake_Cache_getArtifact_x3f___closed__1 = _init_l_Lake_Cache_getArtifact_x3f___closed__1();
lean_mark_persistent(l_Lake_Cache_getArtifact_x3f___closed__1);
l_Lake_Cache_getArtifact___closed__0 = _init_l_Lake_Cache_getArtifact___closed__0();
lean_mark_persistent(l_Lake_Cache_getArtifact___closed__0);
l_Lake_Cache_getArtifactPaths___closed__0 = _init_l_Lake_Cache_getArtifactPaths___closed__0();
lean_mark_persistent(l_Lake_Cache_getArtifactPaths___closed__0);
l_Lake_Cache_outputsDir___closed__0 = _init_l_Lake_Cache_outputsDir___closed__0();
lean_mark_persistent(l_Lake_Cache_outputsDir___closed__0);
l_Lake_Cache_outputsFile___closed__0 = _init_l_Lake_Cache_outputsFile___closed__0();
lean_mark_persistent(l_Lake_Cache_outputsFile___closed__0);
l_Lake_Cache_readOutputs_x3f___closed__0 = _init_l_Lake_Cache_readOutputs_x3f___closed__0();
lean_mark_persistent(l_Lake_Cache_readOutputs_x3f___closed__0);
l_Lake_Cache_readOutputs_x3f___closed__1 = _init_l_Lake_Cache_readOutputs_x3f___closed__1();
lean_mark_persistent(l_Lake_Cache_readOutputs_x3f___closed__1);
l_Lake_Cache_revisionDir___closed__0 = _init_l_Lake_Cache_revisionDir___closed__0();
lean_mark_persistent(l_Lake_Cache_revisionDir___closed__0);
l_Lake_Cache_revisionPath___closed__0 = _init_l_Lake_Cache_revisionPath___closed__0();
lean_mark_persistent(l_Lake_Cache_revisionPath___closed__0);
l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__0 = _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__0();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__0);
l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__1 = _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__1();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__1);
l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__2 = _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__2();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__2);
l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__3 = _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__3();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__3);
l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4 = _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4);
l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5 = _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5);
l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6 = _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6);
l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__7 = _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__7();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__7);
l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__8 = _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__8();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__8);
l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9 = _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9);
l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10 = _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10);
l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11 = _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11);
l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12 = _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12);
l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__13 = _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__13();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__13);
l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__14 = _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__14();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__14);
l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__15 = _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__15();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__15);
l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16 = _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16);
l_Lake_CacheService_reservoirService___closed__0 = _init_l_Lake_CacheService_reservoirService___closed__0();
lean_mark_persistent(l_Lake_CacheService_reservoirService___closed__0);
l_Lake_CacheService_artifactContentType___closed__0 = _init_l_Lake_CacheService_artifactContentType___closed__0();
lean_mark_persistent(l_Lake_CacheService_artifactContentType___closed__0);
l_Lake_CacheService_artifactContentType = _init_l_Lake_CacheService_artifactContentType();
lean_mark_persistent(l_Lake_CacheService_artifactContentType);
l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0 = _init_l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0);
l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__1 = _init_l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__1();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__1);
l_Lake_CacheService_artifactUrl___closed__0 = _init_l_Lake_CacheService_artifactUrl___closed__0();
lean_mark_persistent(l_Lake_CacheService_artifactUrl___closed__0);
l_Lake_CacheService_artifactUrl___closed__1 = _init_l_Lake_CacheService_artifactUrl___closed__1();
lean_mark_persistent(l_Lake_CacheService_artifactUrl___closed__1);
l_Lake_CacheService_artifactUrl___closed__2 = _init_l_Lake_CacheService_artifactUrl___closed__2();
lean_mark_persistent(l_Lake_CacheService_artifactUrl___closed__2);
l_Lake_CacheService_downloadArtifact___closed__0 = _init_l_Lake_CacheService_downloadArtifact___closed__0();
lean_mark_persistent(l_Lake_CacheService_downloadArtifact___closed__0);
l_Lake_CacheService_downloadArtifact___closed__1 = _init_l_Lake_CacheService_downloadArtifact___closed__1();
lean_mark_persistent(l_Lake_CacheService_downloadArtifact___closed__1);
l_Lake_CacheService_downloadArtifact___closed__2 = _init_l_Lake_CacheService_downloadArtifact___closed__2();
lean_mark_persistent(l_Lake_CacheService_downloadArtifact___closed__2);
l_Lake_CacheService_downloadArtifact___closed__3 = _init_l_Lake_CacheService_downloadArtifact___closed__3();
lean_mark_persistent(l_Lake_CacheService_downloadArtifact___closed__3);
l_Lake_CacheService_downloadArtifact___closed__4 = _init_l_Lake_CacheService_downloadArtifact___closed__4();
lean_mark_persistent(l_Lake_CacheService_downloadArtifact___closed__4);
l_Lake_CacheService_downloadArtifact___closed__5 = _init_l_Lake_CacheService_downloadArtifact___closed__5();
l_Lake_CacheService_downloadArtifact___closed__6 = _init_l_Lake_CacheService_downloadArtifact___closed__6();
l_Lake_CacheService_downloadArtifact___closed__7 = _init_l_Lake_CacheService_downloadArtifact___closed__7();
l_Lake_CacheService_downloadArtifacts___closed__0 = _init_l_Lake_CacheService_downloadArtifacts___closed__0();
lean_mark_persistent(l_Lake_CacheService_downloadArtifacts___closed__0);
l_Lake_CacheService_uploadArtifact___closed__0 = _init_l_Lake_CacheService_uploadArtifact___closed__0();
lean_mark_persistent(l_Lake_CacheService_uploadArtifact___closed__0);
l_Lake_CacheService_mapContentType___closed__0 = _init_l_Lake_CacheService_mapContentType___closed__0();
lean_mark_persistent(l_Lake_CacheService_mapContentType___closed__0);
l_Lake_CacheService_mapContentType = _init_l_Lake_CacheService_mapContentType();
lean_mark_persistent(l_Lake_CacheService_mapContentType);
l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__0 = _init_l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__0();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__0);
l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__1 = _init_l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__1();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__1);
l_Lake_CacheService_revisionUrl___closed__0 = _init_l_Lake_CacheService_revisionUrl___closed__0();
lean_mark_persistent(l_Lake_CacheService_revisionUrl___closed__0);
l_Lake_CacheService_revisionUrl___closed__1 = _init_l_Lake_CacheService_revisionUrl___closed__1();
lean_mark_persistent(l_Lake_CacheService_revisionUrl___closed__1);
l_Lake_CacheService_revisionUrl___closed__2 = _init_l_Lake_CacheService_revisionUrl___closed__2();
lean_mark_persistent(l_Lake_CacheService_revisionUrl___closed__2);
l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__0 = _init_l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__0();
lean_mark_persistent(l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__0);
l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__1 = _init_l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__1();
lean_mark_persistent(l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__1);
l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__2 = _init_l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__2();
lean_mark_persistent(l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__2);
l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__3 = _init_l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__3();
lean_mark_persistent(l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__3);
l_Lake_CacheService_uploadRevisionOutputs___closed__0 = _init_l_Lake_CacheService_uploadRevisionOutputs___closed__0();
lean_mark_persistent(l_Lake_CacheService_uploadRevisionOutputs___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

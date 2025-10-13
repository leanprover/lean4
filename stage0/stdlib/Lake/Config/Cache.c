// Lean compiler output
// Module: Lake.Config.Cache
// Imports: public import Lake.Util.Log public import Lake.Config.Artifact public import Lake.Build.Trace import Lake.Config.InstallPath import Lake.Build.Actions import Lake.Util.Url import Lake.Util.Proc import Lake.Util.Reservoir import Lake.Util.IO
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_____private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___Lake_CacheService_uploadArtifacts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_insertCore___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_revisionPath___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifactPaths___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_System_instInhabitedFilePath_default;
LEAN_EXPORT lean_object* l_Lake_Cache_ctorIdx(lean_object*);
lean_object* lean_io_prim_handle_lock(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__3;
lean_object* l_Lean_Json_compress(lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__3;
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadService(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
static uint8_t l_Lake_CacheService_downloadArtifact___closed__6;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__0;
lean_object* l_Lean_JsonNumber_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_CacheService_artifactUrl___closed__0;
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___at_____private_Init_Data_Nat_Control_0__Nat_forM_loop___at___Lake_CacheService_uploadArtifacts_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___Lake_Cache_getArtifactPaths_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_withRepoScope(lean_object*, uint8_t);
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__1;
LEAN_EXPORT lean_object* l_Lake_CacheService_artifactContentType;
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at_____private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lake_CacheMap_get_x3f_spec__0_spec__0___redArg(uint64_t, lean_object*);
lean_object* lean_io_remove_file(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheService_downloadArtifacts_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_CacheService_downloadArtifacts___closed__0;
static lean_object* l_Lake_Cache_getArtifact_x3f___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_CacheService_revisionUrl___closed__1;
static lean_object* l_Lake_Cache_readOutputs_x3f___closed__1;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___at_____private_Init_Data_Nat_Control_0__Nat_forM_loop___at___Lake_CacheService_uploadArtifacts_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_outputsFile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadOutputArtifacts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
static lean_object* l_Lake_Cache_readOutputs_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__13;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Prod_fromJson_x3f___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__8___closed__0;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__4;
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___elam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_split___at_____private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__2___redArg(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___elam__0___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheService_downloadArtifacts_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lake_CacheMap_get_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_updateFile_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_instInhabitedCache_default;
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__15;
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_metadata(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_outputsFile(lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Lake_Cache_artifactDir(lean_object*);
lean_object* l_Lake_download(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputsCore(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_CacheService_downloadArtifact___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_collectOutputDescrs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___at___Lake_CacheService_uploadArtifact_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Reservoir_lakeHeaders;
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadOutputArtifacts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___elam__0___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheService_downloadArtifacts_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_artifactUrl(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_CacheService_revisionUrl___closed__0;
static lean_object* l_Lake_CacheService_downloadArtifact___closed__4;
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__8;
LEAN_EXPORT lean_object* l_List_foldl___at_____private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_insertCore(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Cache_revisionDir___closed__0;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lake_CacheMap_parse___closed__0;
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5;
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lake_CacheMap_get_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_mapContentType;
lean_object* l_Lake_Hash_hex(uint64_t);
static lean_object* l_Lake_CacheMap_updateFile___closed__1;
LEAN_EXPORT lean_object* l_Lake_CacheService_ctorIdx___boxed(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Cache_outputsFile___closed__0;
LEAN_EXPORT lean_object* l_Lake_Cache_outputsDir(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___Lake_CacheService_uploadArtifacts_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_CacheMap_updateFile_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_CacheService_mapContentType___closed__0;
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifactPaths(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12;
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadRevisionOutputs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__7;
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
static lean_object* l_Lake_CacheService_artifactUrl___closed__1;
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__2(lean_object*, uint64_t, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheRef_get_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__0;
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedCache;
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_CacheMap_updateFile_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_CacheService_downloadArtifact___closed__2;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lake_CacheService_downloadArtifact___closed__0;
lean_object* l_Lake_createParentDirs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at_____private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lake_CacheMap_get_x3f_spec__0_spec__0(lean_object*, uint64_t, lean_object*);
static lean_object* l_Lake_CacheMap_parse___closed__1;
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__2;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_Cache_writeMap_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_IO_FS_Handle_putStrLn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact___at___Lake_CacheService_uploadArtifacts___elam__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Lake_CacheMap_schemaVersion___closed__0;
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_writeFile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_artifactUrl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_get_x3f___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___at___Lake_CacheService_uploadArtifact_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__3;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_CacheMap_updateFile_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_updateFile(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_CacheMap_collectOutputDescrs___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___Lake_CacheService_uploadArtifacts_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_updateFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_reservoirService(lean_object*, uint8_t);
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__0;
static lean_object* l_Lake_CacheService_downloadArtifact___closed__1;
static lean_object* l_Lake_Cache_outputsDir___closed__0;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifactPaths___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3___redArg(lean_object*);
lean_object* l_Lake_Hash_instHashable___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_schemaVersion;
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_get_x3f(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_readOutputs_x3f(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___at_____private_Init_Data_Nat_Control_0__Nat_forM_loop___at___Lake_CacheService_uploadArtifacts_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_revisionUrl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_revisionDir(lean_object*);
lean_object* l_String_posOfAux(lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputsCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Cache_artifactDir___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lake_CacheMap_get_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lake_ArtifactDescr_ofFilePath_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lake_CacheService_revisionUrl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16;
LEAN_EXPORT lean_object* l_Lake_Cache_writeMap(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Cache_revisionPath___closed__0;
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_Cache_writeMap_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_artifactPath___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Cache_writeMap_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lake_CacheMap_parse___closed__4;
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact___at___Lake_CacheService_uploadArtifacts___elam__0_spec__0(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_____private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_updateFile_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_CacheService_uploadArtifact___closed__0;
static lean_object* l_Lake_CacheMap_load___closed__0;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__1;
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact___at___Lake_CacheService_downloadArtifacts___elam__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_revisionPath(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_CacheService_reservoirService___closed__0;
LEAN_EXPORT lean_object* l_Lake_Cache_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3_spec__3_spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__1;
static lean_object* l_Lake_CacheService_artifactUrl___closed__2;
static lean_object* l_Lake_CacheService_uploadRevisionOutputs___closed__0;
lean_object* lean_io_prim_handle_get_line(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Hash_ofJsonNumber_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheRef_mk(lean_object*, lean_object*);
lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheService_downloadArtifacts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Prod_toJson___at___Lake_CacheMap_updateFile_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadService(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__14;
static lean_object* l_Lake_CacheMap_writeFile___closed__1;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lake_CacheMap_get_x3f_spec__0(lean_object*, lean_object*, uint64_t);
static lean_object* l_Lake_CacheMap_parse___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_updateFile_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lake_CacheMap_parse___closed__2;
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11;
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact___at___Lake_CacheService_downloadArtifacts___elam__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_CacheMap_updateFile___closed__0;
static lean_object* l_Lake_Cache_getArtifactPaths___closed__0;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifactPaths___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4;
static lean_object* l_Lake_instInhabitedCache_default___closed__0;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
static lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__2;
static lean_object* l_Lake_Cache_artifactPath___closed__0;
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___at___Lake_CacheService_downloadOutputArtifacts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtsService(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___Lake_Cache_getArtifactPaths_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_CacheMap_writeFile___closed__0;
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_toJson___at___Lake_CacheMap_updateFile_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___at_____private_Init_Data_Nat_Control_0__Nat_forM_loop___at___Lake_CacheService_uploadArtifacts_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___at___Lake_CacheService_downloadOutputArtifacts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lake_CacheMap_get_x3f_spec__0___redArg(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__6___redArg(uint64_t, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Lake_uriEncode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(uint64_t, lean_object*, lean_object*);
static lean_object* l_Lake_CacheMap_parse___closed__5;
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_CacheMap_collectOutputDescrs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2(lean_object*, lean_object*, uint64_t, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__2;
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadRevisionOutputs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact(uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___Lake_Cache_getArtifactPaths_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0;
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___redArg(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_writeMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_readOutputs_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_load(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_reservoirService___boxed(lean_object*, lean_object*);
static size_t l_Lake_CacheService_downloadArtifact___closed__7;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_updateFile_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3_spec__3_spec__3___redArg(lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
static lean_object* l_Lake_Cache_getArtifact___closed__0;
size_t lean_usize_sub(size_t, size_t);
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_CacheMap_updateFile_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___redArg(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___redArg(lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_CacheMap_updateFile_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__2;
LEAN_EXPORT lean_object* l_String_split___at_____private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lake_Cache_getArtifact_x3f___closed__0;
lean_object* lean_io_error_to_string(lean_object*);
static uint8_t l_Lake_CacheService_downloadArtifact___closed__5;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__1;
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs(lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_load_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Cache_writeMap_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_computeBinFileHash(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lake_CacheMap_get_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_collectOutputDescrs_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheRef_get_x3f(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___Lake_CacheService_uploadArtifacts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_artifactPath(lean_object*, uint64_t, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lake_instDecidableEqHash___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___Lake_Cache_getArtifactPaths_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__6(lean_object*, uint64_t, lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6;
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_io_prim_handle_rewind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Hash_fromJson_x3f(lean_object*);
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9;
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__1;
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*);
static lean_object* l_Lake_CacheService_revisionUrl___closed__2;
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___redArg(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_getUrl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_collectOutputDescrs(lean_object*, lean_object*, lean_object*);
static lean_object* l_Prod_fromJson_x3f___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__8___closed__1;
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
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_string_utf8_byte_size(x_2);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_16, x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = l_Lean_Json_parse(x_2);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_5 = x_20;
goto block_15;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = l_Lean_Json_getStr_x3f(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_5 = x_23;
goto block_15;
}
else
{
lean_object* x_24; lean_object* x_37; uint8_t x_38; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec_ref(x_22);
x_37 = l_Lake_CacheMap_schemaVersion___closed__0;
x_38 = lean_string_dec_eq(x_24, x_37);
if (x_38 == 0)
{
goto block_36;
}
else
{
if (x_18 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_24);
lean_dec_ref(x_1);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_3);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_4);
return x_41;
}
else
{
goto block_36;
}
}
block_36:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_25 = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__1;
x_26 = lean_string_append(x_1, x_25);
x_27 = lean_string_append(x_26, x_24);
lean_dec(x_24);
x_28 = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__2;
x_29 = lean_string_append(x_27, x_28);
x_30 = 2;
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_30);
x_32 = lean_box(0);
x_33 = lean_array_push(x_3, x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_4);
return x_35;
}
}
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec_ref(x_2);
x_42 = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__3;
x_43 = lean_string_append(x_1, x_42);
x_44 = 3;
x_45 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_44);
x_46 = lean_array_get_size(x_3);
x_47 = lean_array_push(x_3, x_45);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_4);
return x_49;
}
block_15:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
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
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__2___redArg(uint64_t x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__2(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3_spec__3_spec__3___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3_spec__3_spec__3___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3_spec__3___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3___redArg(lean_object* x_1) {
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
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3_spec__3___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__6___redArg(uint64_t x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__6___redArg(x_1, x_2, x_7);
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
x_17 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__6___redArg(x_1, x_2, x_14);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__6(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__6___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___redArg(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
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
x_20 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__2___redArg(x_2, x_19);
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
x_32 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3___redArg(x_25);
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
x_35 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__6___redArg(x_2, x_3, x_19);
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
x_52 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__2___redArg(x_2, x_51);
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
x_64 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__3___redArg(x_57);
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
x_69 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__6___redArg(x_2, x_3, x_51);
x_70 = lean_array_uset(x_68, x_50, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_37);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Prod_fromJson_x3f___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__8___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected pair, got '", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Prod_fromJson_x3f___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__8(lean_object* x_1) {
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
x_3 = l_Prod_fromJson_x3f___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__8___closed__0;
x_4 = lean_unsigned_to_nat(80u);
x_5 = l_Lean_Json_pretty(x_2, x_4);
x_6 = lean_string_append(x_3, x_5);
lean_dec_ref(x_5);
x_7 = l_Prod_fromJson_x3f___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__8___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": invalid JSON on line ", 23, 23);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint32_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_20; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_9 = 10;
lean_inc(x_7);
x_10 = l_String_posOfAux(x_3, x_9, x_6, x_7);
x_37 = lean_string_utf8_extract(x_3, x_7, x_10);
lean_dec(x_7);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_string_utf8_byte_size(x_37);
x_40 = l_Substring_takeWhileAux___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__0(x_37, x_39, x_38);
x_41 = l_Substring_takeRightWhileAux___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__1(x_37, x_40, x_39);
x_42 = lean_string_utf8_extract(x_37, x_40, x_41);
lean_dec(x_41);
lean_dec(x_40);
x_43 = lean_string_utf8_byte_size(x_42);
lean_dec_ref(x_42);
x_44 = lean_nat_dec_eq(x_43, x_38);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = l_Lean_Json_parse(x_37);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_20 = x_46;
goto block_36;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec_ref(x_45);
x_48 = l_Prod_fromJson_x3f___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__8(x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
x_20 = x_49;
goto block_36;
}
else
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec_ref(x_48);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; uint64_t x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
x_54 = lean_unbox_uint64(x_52);
lean_dec(x_52);
x_55 = l_Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___redArg(x_5, x_54, x_53);
lean_inc_ref(x_55);
lean_ctor_set(x_50, 1, x_8);
lean_ctor_set(x_50, 0, x_55);
x_11 = x_50;
x_12 = x_55;
x_13 = x_8;
goto block_19;
}
else
{
lean_object* x_56; lean_object* x_57; uint64_t x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_50, 0);
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_50);
x_58 = lean_unbox_uint64(x_56);
lean_dec(x_56);
x_59 = l_Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___redArg(x_5, x_58, x_57);
lean_inc_ref(x_59);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_8);
x_11 = x_60;
x_12 = x_59;
x_13 = x_8;
goto block_19;
}
}
}
}
else
{
lean_object* x_61; 
lean_dec_ref(x_37);
lean_dec(x_10);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_5);
lean_ctor_set(x_61, 1, x_8);
return x_61;
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
x_8 = x_13;
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
block_36:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_21 = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__0;
lean_inc_ref(x_2);
x_22 = lean_string_append(x_2, x_21);
lean_inc(x_4);
x_23 = l_Nat_reprFast(x_4);
x_24 = lean_string_append(x_22, x_23);
lean_dec_ref(x_23);
x_25 = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__1;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_string_append(x_26, x_20);
lean_dec_ref(x_20);
x_28 = 2;
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
lean_inc_ref(x_1);
x_30 = lean_apply_2(x_1, x_29, x_8);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 1);
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
lean_inc(x_32);
lean_inc_ref(x_5);
lean_ctor_set(x_30, 0, x_5);
x_11 = x_30;
x_12 = x_5;
x_13 = x_32;
goto block_19;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
lean_inc(x_34);
lean_inc_ref(x_5);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_5);
lean_ctor_set(x_35, 1, x_34);
x_11 = x_35;
x_12 = x_5;
x_13 = x_34;
goto block_19;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint32_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_20; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_9 = 10;
lean_inc(x_6);
x_10 = l_String_posOfAux(x_2, x_9, x_5, x_6);
x_37 = lean_string_utf8_extract(x_2, x_6, x_10);
lean_dec(x_6);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_string_utf8_byte_size(x_37);
x_40 = l_Substring_takeWhileAux___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__0(x_37, x_39, x_38);
x_41 = l_Substring_takeRightWhileAux___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__1(x_37, x_40, x_39);
x_42 = lean_string_utf8_extract(x_37, x_40, x_41);
lean_dec(x_41);
lean_dec(x_40);
x_43 = lean_string_utf8_byte_size(x_42);
lean_dec_ref(x_42);
x_44 = lean_nat_dec_eq(x_43, x_38);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = l_Lean_Json_parse(x_37);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_20 = x_46;
goto block_36;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec_ref(x_45);
x_48 = l_Prod_fromJson_x3f___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__8(x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
x_20 = x_49;
goto block_36;
}
else
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec_ref(x_48);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; uint64_t x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
x_54 = lean_unbox_uint64(x_52);
lean_dec(x_52);
x_55 = l_Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___redArg(x_4, x_54, x_53);
lean_inc_ref(x_55);
lean_ctor_set(x_50, 1, x_8);
lean_ctor_set(x_50, 0, x_55);
x_11 = x_50;
x_12 = x_55;
x_13 = x_8;
goto block_19;
}
else
{
lean_object* x_56; lean_object* x_57; uint64_t x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_50, 0);
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_50);
x_58 = lean_unbox_uint64(x_56);
lean_dec(x_56);
x_59 = l_Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___redArg(x_4, x_58, x_57);
lean_inc_ref(x_59);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_8);
x_11 = x_60;
x_12 = x_59;
x_13 = x_8;
goto block_19;
}
}
}
}
else
{
lean_object* x_61; 
lean_dec_ref(x_37);
lean_dec(x_10);
lean_dec_ref(x_7);
lean_dec(x_3);
lean_dec_ref(x_1);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_4);
lean_ctor_set(x_61, 1, x_8);
return x_61;
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
x_18 = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0(x_7, x_1, x_2, x_16, x_12, x_5, x_17, x_13);
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
block_36:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_21 = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__0;
lean_inc_ref(x_1);
x_22 = lean_string_append(x_1, x_21);
lean_inc(x_3);
x_23 = l_Nat_reprFast(x_3);
x_24 = lean_string_append(x_22, x_23);
lean_dec_ref(x_23);
x_25 = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__1;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_string_append(x_26, x_20);
lean_dec_ref(x_20);
x_28 = 2;
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
lean_inc_ref(x_7);
x_30 = lean_apply_2(x_7, x_29, x_8);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 1);
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
lean_inc(x_32);
lean_inc_ref(x_4);
lean_ctor_set(x_30, 0, x_4);
x_11 = x_30;
x_12 = x_4;
x_13 = x_32;
goto block_19;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
lean_inc(x_34);
lean_inc_ref(x_4);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_4);
lean_ctor_set(x_35, 1, x_34);
x_11 = x_35;
x_12 = x_4;
x_13 = x_34;
goto block_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeWhileAux___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeRightWhileAux___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__2___redArg(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__2(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__6___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_6 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2_spec__6(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___redArg(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_6 = l_Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_2(x_2, x_1, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CacheMap_parse___elam__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___elam__0___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CacheMap_parse___elam__0___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0_spec__0___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_8 = lean_array_uget(x_1, x_2);
lean_inc_ref(x_5);
x_9 = l_Lake_CacheMap_parse___elam__0___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0_spec__0___redArg(x_5, x_8, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_10;
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_15; 
lean_dec_ref(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_6);
return x_15;
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
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint32_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_9 = 10;
x_10 = lean_string_utf8_byte_size(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_String_posOfAux(x_2, x_9, x_10, x_11);
x_22 = lean_string_utf8_extract(x_2, x_11, x_12);
x_23 = lean_string_utf8_byte_size(x_22);
x_24 = l_Substring_takeWhileAux___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__0(x_22, x_23, x_11);
x_25 = l_Substring_takeRightWhileAux___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__1(x_22, x_24, x_23);
x_26 = lean_string_utf8_extract(x_22, x_24, x_25);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_22);
x_27 = l_Lake_CacheMap_parse___closed__5;
lean_inc_ref(x_1);
x_28 = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(x_1, x_26, x_27, x_4);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec_ref(x_29);
x_32 = lean_array_get_size(x_31);
x_33 = lean_nat_dec_lt(x_11, x_32);
if (x_33 == 0)
{
lean_dec(x_32);
lean_dec(x_31);
x_13 = x_30;
goto block_21;
}
else
{
uint8_t x_34; 
x_34 = lean_nat_dec_le(x_32, x_32);
if (x_34 == 0)
{
lean_dec(x_32);
lean_dec(x_31);
x_13 = x_30;
goto block_21;
}
else
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_box(0);
x_36 = 0;
x_37 = lean_usize_of_nat(x_32);
lean_dec(x_32);
lean_inc_ref(x_3);
x_38 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0(x_31, x_36, x_37, x_35, x_3, x_30);
lean_dec(x_31);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec_ref(x_38);
x_13 = x_39;
goto block_21;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_1);
x_40 = !lean_is_exclusive(x_28);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_28, 1);
x_42 = lean_ctor_get(x_28, 0);
lean_dec(x_42);
x_43 = lean_ctor_get(x_29, 1);
lean_inc(x_43);
lean_dec_ref(x_29);
x_44 = lean_array_get_size(x_43);
x_45 = lean_nat_dec_lt(x_11, x_44);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec_ref(x_3);
x_46 = lean_box(0);
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 0, x_46);
return x_28;
}
else
{
uint8_t x_47; 
lean_free_object(x_28);
x_47 = lean_nat_dec_le(x_44, x_44);
if (x_47 == 0)
{
lean_dec(x_44);
lean_dec(x_43);
lean_dec_ref(x_3);
x_5 = x_41;
goto block_8;
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_box(0);
x_49 = 0;
x_50 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_51 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0(x_43, x_49, x_50, x_48, x_3, x_41);
lean_dec(x_43);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec_ref(x_51);
x_5 = x_52;
goto block_8;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_28, 1);
lean_inc(x_53);
lean_dec(x_28);
x_54 = lean_ctor_get(x_29, 1);
lean_inc(x_54);
lean_dec_ref(x_29);
x_55 = lean_array_get_size(x_54);
x_56 = lean_nat_dec_lt(x_11, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_3);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_53);
return x_58;
}
else
{
uint8_t x_59; 
x_59 = lean_nat_dec_le(x_55, x_55);
if (x_59 == 0)
{
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_3);
x_5 = x_53;
goto block_8;
}
else
{
lean_object* x_60; size_t x_61; size_t x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_box(0);
x_61 = 0;
x_62 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_63 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0(x_54, x_61, x_62, x_60, x_3, x_53);
lean_dec(x_54);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec_ref(x_63);
x_5 = x_64;
goto block_8;
}
}
}
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
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
x_18 = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0(x_3, x_1, x_2, x_15, x_16, x_10, x_17, x_13);
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
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_13);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_CacheMap_parse(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_io_prim_handle_get_line(x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_26 = lean_string_utf8_byte_size(x_9);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_eq(x_26, x_27);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; 
lean_free_object(x_7);
x_29 = l_Lean_Json_parse(x_9);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_11 = x_30;
goto block_25;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec_ref(x_29);
x_32 = l_Prod_fromJson_x3f___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__8(x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_11 = x_33;
goto block_25;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint64_t x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_3, x_37);
lean_dec(x_3);
x_39 = lean_unbox_uint64(x_35);
lean_dec(x_35);
x_40 = l_Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___redArg(x_4, x_39, x_36);
x_3 = x_38;
x_4 = x_40;
x_6 = x_10;
goto _start;
}
}
}
else
{
lean_object* x_42; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec_ref(x_2);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_4);
lean_ctor_set(x_42, 1, x_5);
lean_ctor_set(x_7, 0, x_42);
return x_7;
}
block_25:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_12 = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__0;
lean_inc_ref(x_2);
x_13 = lean_string_append(x_2, x_12);
lean_inc(x_3);
x_14 = l_Nat_reprFast(x_3);
x_15 = lean_string_append(x_13, x_14);
lean_dec_ref(x_14);
x_16 = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_string_append(x_17, x_11);
lean_dec_ref(x_11);
x_19 = 2;
x_20 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_19);
x_21 = lean_array_push(x_5, x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_3, x_22);
lean_dec(x_3);
x_3 = x_23;
x_5 = x_21;
x_6 = x_10;
goto _start;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_43 = lean_ctor_get(x_7, 0);
x_44 = lean_ctor_get(x_7, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_7);
x_60 = lean_string_utf8_byte_size(x_43);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_nat_dec_eq(x_60, x_61);
lean_dec(x_60);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = l_Lean_Json_parse(x_43);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_45 = x_64;
goto block_59;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
lean_dec_ref(x_63);
x_66 = l_Prod_fromJson_x3f___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__8(x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec_ref(x_66);
x_45 = x_67;
goto block_59;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint64_t x_73; lean_object* x_74; 
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
lean_dec_ref(x_66);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_unsigned_to_nat(1u);
x_72 = lean_nat_add(x_3, x_71);
lean_dec(x_3);
x_73 = lean_unbox_uint64(x_69);
lean_dec(x_69);
x_74 = l_Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___redArg(x_4, x_73, x_70);
x_3 = x_72;
x_4 = x_74;
x_6 = x_44;
goto _start;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_43);
lean_dec(x_3);
lean_dec_ref(x_2);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_4);
lean_ctor_set(x_76, 1, x_5);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_44);
return x_77;
}
block_59:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_46 = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__0;
lean_inc_ref(x_2);
x_47 = lean_string_append(x_2, x_46);
lean_inc(x_3);
x_48 = l_Nat_reprFast(x_3);
x_49 = lean_string_append(x_47, x_48);
lean_dec_ref(x_48);
x_50 = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__1;
x_51 = lean_string_append(x_49, x_50);
x_52 = lean_string_append(x_51, x_45);
lean_dec_ref(x_45);
x_53 = 2;
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_53);
x_55 = lean_array_push(x_5, x_54);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_add(x_3, x_56);
lean_dec(x_3);
x_3 = x_57;
x_5 = x_55;
x_6 = x_44;
goto _start;
}
}
}
else
{
uint8_t x_78; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_78 = !lean_is_exclusive(x_7);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_79 = lean_ctor_get(x_7, 0);
x_80 = lean_io_error_to_string(x_79);
x_81 = 3;
x_82 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set_uint8(x_82, sizeof(void*)*1, x_81);
x_83 = lean_array_get_size(x_5);
x_84 = lean_array_push(x_5, x_82);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_85);
return x_7;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_86 = lean_ctor_get(x_7, 0);
x_87 = lean_ctor_get(x_7, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_7);
x_88 = lean_io_error_to_string(x_86);
x_89 = 3;
x_90 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set_uint8(x_90, sizeof(void*)*1, x_89);
x_91 = lean_array_get_size(x_5);
x_92 = lean_array_push(x_5, x_90);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_87);
return x_94;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_prim_handle_get_line(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
lean_inc_ref(x_2);
x_8 = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(x_2, x_6, x_3, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_unsigned_to_nat(2u);
x_13 = l_Lake_CacheMap_parse___closed__4;
x_14 = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(x_1, x_2, x_12, x_13, x_11, x_10);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec_ref(x_2);
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_8, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_8;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_8, 0, x_20);
return x_8;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_dec(x_8);
x_22 = lean_ctor_get(x_9, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_24 = x_9;
} else {
 lean_dec_ref(x_9);
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
lean_dec_ref(x_2);
x_27 = !lean_is_exclusive(x_5);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_io_error_to_string(x_28);
x_30 = 3;
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_30);
x_32 = lean_array_get_size(x_3);
x_33 = lean_array_push(x_3, x_31);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_34);
return x_5;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_5, 0);
x_36 = lean_ctor_get(x_5, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_5);
x_37 = lean_io_error_to_string(x_35);
x_38 = 3;
x_39 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_38);
x_40 = lean_array_get_size(x_3);
x_41 = lean_array_push(x_3, x_39);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_36);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore(x_1, x_2, x_3, x_4);
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
LEAN_EXPORT lean_object* l_Lake_CacheMap_load(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = 0;
x_5 = lean_io_prim_handle_mk(x_1, x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = 0;
x_9 = lean_io_prim_handle_lock(x_6, x_8, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_io_prim_handle_get_line(x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
lean_inc_ref(x_1);
x_14 = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(x_1, x_12, x_2, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_unsigned_to_nat(2u);
x_19 = l_Lake_CacheMap_parse___closed__4;
x_20 = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(x_6, x_1, x_18, x_19, x_17, x_16);
lean_dec(x_6);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_6);
lean_dec_ref(x_1);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_14, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_14;
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
lean_ctor_set(x_14, 0, x_26);
return x_14;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_dec(x_14);
x_28 = lean_ctor_get(x_15, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_30 = x_15;
} else {
 lean_dec_ref(x_15);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(1, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_6);
lean_dec_ref(x_1);
x_33 = !lean_is_exclusive(x_11);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_11, 0);
x_35 = lean_io_error_to_string(x_34);
x_36 = 3;
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_36);
x_38 = lean_array_get_size(x_2);
x_39 = lean_array_push(x_2, x_37);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set_tag(x_11, 0);
lean_ctor_set(x_11, 0, x_40);
return x_11;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_11, 0);
x_42 = lean_ctor_get(x_11, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_11);
x_43 = lean_io_error_to_string(x_41);
x_44 = 3;
x_45 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_44);
x_46 = lean_array_get_size(x_2);
x_47 = lean_array_push(x_2, x_45);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_42);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_6);
lean_dec_ref(x_1);
x_50 = !lean_is_exclusive(x_9);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_51 = lean_ctor_get(x_9, 0);
x_52 = lean_io_error_to_string(x_51);
x_53 = 3;
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_53);
x_55 = lean_array_get_size(x_2);
x_56 = lean_array_push(x_2, x_54);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set_tag(x_9, 0);
lean_ctor_set(x_9, 0, x_57);
return x_9;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_58 = lean_ctor_get(x_9, 0);
x_59 = lean_ctor_get(x_9, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_9);
x_60 = lean_io_error_to_string(x_58);
x_61 = 3;
x_62 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_61);
x_63 = lean_array_get_size(x_2);
x_64 = lean_array_push(x_2, x_62);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_59);
return x_66;
}
}
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_5);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_68 = lean_ctor_get(x_5, 0);
x_69 = l_Lake_CacheMap_load___closed__0;
x_70 = lean_string_append(x_1, x_69);
x_71 = lean_io_error_to_string(x_68);
x_72 = lean_string_append(x_70, x_71);
lean_dec_ref(x_71);
x_73 = 3;
x_74 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set_uint8(x_74, sizeof(void*)*1, x_73);
x_75 = lean_array_get_size(x_2);
x_76 = lean_array_push(x_2, x_74);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_77);
return x_5;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_78 = lean_ctor_get(x_5, 0);
x_79 = lean_ctor_get(x_5, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_5);
x_80 = l_Lake_CacheMap_load___closed__0;
x_81 = lean_string_append(x_1, x_80);
x_82 = lean_io_error_to_string(x_78);
x_83 = lean_string_append(x_81, x_82);
lean_dec_ref(x_82);
x_84 = 3;
x_85 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set_uint8(x_85, sizeof(void*)*1, x_84);
x_86 = lean_array_get_size(x_2);
x_87 = lean_array_push(x_2, x_85);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_79);
return x_89;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_load_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_10; lean_object* x_11; 
x_10 = 0;
x_11 = lean_io_prim_handle_mk(x_1, x_10, x_3);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = 0;
x_15 = lean_io_prim_handle_lock(x_12, x_14, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_io_prim_handle_get_line(x_12, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
lean_inc_ref(x_1);
x_20 = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(x_1, x_18, x_2, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = lean_unsigned_to_nat(2u);
x_25 = l_Lake_CacheMap_parse___closed__4;
x_26 = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(x_12, x_1, x_24, x_25, x_23, x_22);
lean_dec(x_12);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_27, 0, x_32);
return x_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_27, 0);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_27);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_26, 0, x_36);
return x_26;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_26, 1);
lean_inc(x_37);
lean_dec(x_26);
x_38 = lean_ctor_get(x_27, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_27, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_40 = x_27;
} else {
 lean_dec_ref(x_27);
 x_40 = lean_box(0);
}
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_38);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_37);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_26, 1);
lean_inc(x_44);
lean_dec_ref(x_26);
x_45 = lean_ctor_get(x_27, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_27, 1);
lean_inc(x_46);
lean_dec_ref(x_27);
x_4 = x_45;
x_5 = x_46;
x_6 = x_44;
goto block_9;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_12);
lean_dec_ref(x_1);
x_47 = lean_ctor_get(x_20, 1);
lean_inc(x_47);
lean_dec_ref(x_20);
x_48 = lean_ctor_get(x_21, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_21, 1);
lean_inc(x_49);
lean_dec_ref(x_21);
x_4 = x_48;
x_5 = x_49;
x_6 = x_47;
goto block_9;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_12);
lean_dec_ref(x_1);
x_50 = lean_ctor_get(x_17, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_17, 1);
lean_inc(x_51);
lean_dec_ref(x_17);
x_52 = lean_io_error_to_string(x_50);
x_53 = 3;
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_53);
x_55 = lean_array_get_size(x_2);
x_56 = lean_array_push(x_2, x_54);
x_4 = x_55;
x_5 = x_56;
x_6 = x_51;
goto block_9;
}
}
else
{
uint8_t x_57; 
lean_dec(x_12);
lean_dec_ref(x_1);
x_57 = !lean_is_exclusive(x_15);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_58 = lean_ctor_get(x_15, 0);
x_59 = lean_io_error_to_string(x_58);
x_60 = 3;
x_61 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_60);
x_62 = lean_array_get_size(x_2);
x_63 = lean_array_push(x_2, x_61);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set_tag(x_15, 0);
lean_ctor_set(x_15, 0, x_64);
return x_15;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_65 = lean_ctor_get(x_15, 0);
x_66 = lean_ctor_get(x_15, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_15);
x_67 = lean_io_error_to_string(x_65);
x_68 = 3;
x_69 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set_uint8(x_69, sizeof(void*)*1, x_68);
x_70 = lean_array_get_size(x_2);
x_71 = lean_array_push(x_2, x_69);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_66);
return x_73;
}
}
}
else
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_11, 0);
lean_inc(x_74);
if (lean_obj_tag(x_74) == 11)
{
uint8_t x_75; 
lean_dec_ref(x_74);
lean_dec_ref(x_1);
x_75 = !lean_is_exclusive(x_11);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_11, 0);
lean_dec(x_76);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_2);
lean_ctor_set_tag(x_11, 0);
lean_ctor_set(x_11, 0, x_78);
return x_11;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_11, 1);
lean_inc(x_79);
lean_dec(x_11);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_2);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_79);
return x_82;
}
}
else
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_11);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_84 = lean_ctor_get(x_11, 0);
lean_dec(x_84);
x_85 = l_Lake_CacheMap_load___closed__0;
x_86 = lean_string_append(x_1, x_85);
x_87 = lean_io_error_to_string(x_74);
x_88 = lean_string_append(x_86, x_87);
lean_dec_ref(x_87);
x_89 = 3;
x_90 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set_uint8(x_90, sizeof(void*)*1, x_89);
x_91 = lean_array_get_size(x_2);
x_92 = lean_array_push(x_2, x_90);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set_tag(x_11, 0);
lean_ctor_set(x_11, 0, x_93);
return x_11;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_94 = lean_ctor_get(x_11, 1);
lean_inc(x_94);
lean_dec(x_11);
x_95 = l_Lake_CacheMap_load___closed__0;
x_96 = lean_string_append(x_1, x_95);
x_97 = lean_io_error_to_string(x_74);
x_98 = lean_string_append(x_96, x_97);
lean_dec_ref(x_97);
x_99 = 3;
x_100 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set_uint8(x_100, sizeof(void*)*1, x_99);
x_101 = lean_array_get_size(x_2);
x_102 = lean_array_push(x_2, x_100);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_94);
return x_104;
}
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
}
static lean_object* _init_l_Prod_toJson___at___Lake_CacheMap_updateFile_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Prod_toJson___at___Lake_CacheMap_updateFile_spec__0(lean_object* x_1) {
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
x_7 = l_Prod_toJson___at___Lake_CacheMap_updateFile_spec__0___closed__0;
x_8 = lean_array_push(x_7, x_6);
x_9 = lean_array_push(x_8, x_3);
x_10 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_CacheMap_updateFile_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_9);
lean_inc(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Prod_toJson___at___Lake_CacheMap_updateFile_spec__0(x_11);
x_13 = l_Lean_Json_compress(x_12);
x_14 = l_IO_FS_Handle_putStrLn(x_1, x_13, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_2 = x_15;
x_3 = x_10;
x_5 = x_16;
goto _start;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_io_error_to_string(x_19);
x_21 = 3;
x_22 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_21);
x_23 = lean_array_get_size(x_4);
x_24 = lean_array_push(x_4, x_22);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_28 = lean_io_error_to_string(x_26);
x_29 = 3;
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_29);
x_31 = lean_array_get_size(x_4);
x_32 = lean_array_push(x_4, x_30);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_27);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_updateFile_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_3, x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_array_uget(x_2, x_3);
x_10 = lean_box(0);
x_11 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_CacheMap_updateFile_spec__1(x_1, x_10, x_9, x_6, x_7);
lean_dec(x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec_ref(x_12);
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_3 = x_17;
x_5 = x_14;
x_6 = x_15;
x_7 = x_13;
goto _start;
}
else
{
lean_dec_ref(x_12);
return x_11;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_6);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_7);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_CacheMap_updateFile_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___redArg(x_1, x_6, x_4);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_CacheMap_updateFile_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_CacheMap_updateFile_spec__3___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_updateFile_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_8 = lean_array_uget(x_3, x_4);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_CacheMap_updateFile_spec__3___redArg(x_6, x_8);
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
LEAN_EXPORT lean_object* l_Lake_CacheMap_updateFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_11; 
x_11 = l_Lake_createParentDirs(x_1, x_4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = 4;
x_14 = lean_io_prim_handle_mk(x_1, x_13, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = 3;
x_17 = lean_io_prim_handle_mk(x_1, x_16, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = 1;
x_21 = lean_io_prim_handle_lock(x_18, x_20, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_io_prim_handle_get_line(x_18, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
lean_inc_ref(x_1);
x_26 = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(x_1, x_24, x_3, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec_ref(x_27);
x_30 = lean_unsigned_to_nat(2u);
x_31 = lean_unsigned_to_nat(0u);
x_32 = l_Lake_CacheMap_parse___closed__4;
x_33 = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(x_18, x_1, x_30, x_32, x_29, x_28);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_38 = x_34;
} else {
 lean_dec_ref(x_34);
 x_38 = lean_box(0);
}
x_85 = lean_ctor_get(x_2, 1);
x_86 = lean_array_get_size(x_85);
x_87 = lean_nat_dec_lt(x_31, x_86);
if (x_87 == 0)
{
lean_dec(x_86);
x_39 = x_36;
goto block_84;
}
else
{
uint8_t x_88; 
x_88 = lean_nat_dec_le(x_86, x_86);
if (x_88 == 0)
{
lean_dec(x_86);
x_39 = x_36;
goto block_84;
}
else
{
lean_object* x_89; lean_object* x_90; size_t x_91; size_t x_92; lean_object* x_93; 
x_89 = l_Lake_CacheMap_updateFile___closed__0;
x_90 = l_Lake_CacheMap_updateFile___closed__1;
x_91 = 0;
x_92 = lean_usize_of_nat(x_86);
lean_dec(x_86);
x_93 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_updateFile_spec__4(x_90, x_89, x_85, x_91, x_92, x_36);
x_39 = x_93;
goto block_84;
}
}
block_84:
{
lean_object* x_40; 
x_40 = lean_io_prim_handle_rewind(x_18, x_35);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_42 = lean_ctor_get(x_40, 1);
x_43 = lean_ctor_get(x_40, 0);
lean_dec(x_43);
x_44 = lean_ctor_get(x_39, 1);
lean_inc_ref(x_44);
lean_dec_ref(x_39);
x_45 = lean_array_get_size(x_44);
x_46 = lean_box(0);
x_47 = lean_nat_dec_lt(x_31, x_45);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_18);
if (lean_is_scalar(x_38)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_38;
}
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_37);
lean_ctor_set(x_40, 0, x_48);
return x_40;
}
else
{
uint8_t x_49; 
x_49 = lean_nat_dec_le(x_45, x_45);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_18);
if (lean_is_scalar(x_38)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_38;
}
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_37);
lean_ctor_set(x_40, 0, x_50);
return x_40;
}
else
{
size_t x_51; size_t x_52; lean_object* x_53; 
lean_free_object(x_40);
lean_dec(x_38);
x_51 = 0;
x_52 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_53 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_updateFile_spec__2(x_18, x_44, x_51, x_52, x_46, x_37, x_42);
lean_dec_ref(x_44);
lean_dec(x_18);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_40, 1);
lean_inc(x_54);
lean_dec(x_40);
x_55 = lean_ctor_get(x_39, 1);
lean_inc_ref(x_55);
lean_dec_ref(x_39);
x_56 = lean_array_get_size(x_55);
x_57 = lean_box(0);
x_58 = lean_nat_dec_lt(x_31, x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_18);
if (lean_is_scalar(x_38)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_38;
}
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_37);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_54);
return x_60;
}
else
{
uint8_t x_61; 
x_61 = lean_nat_dec_le(x_56, x_56);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_18);
if (lean_is_scalar(x_38)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_38;
}
lean_ctor_set(x_62, 0, x_57);
lean_ctor_set(x_62, 1, x_37);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_54);
return x_63;
}
else
{
size_t x_64; size_t x_65; lean_object* x_66; 
lean_dec(x_38);
x_64 = 0;
x_65 = lean_usize_of_nat(x_56);
lean_dec(x_56);
x_66 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_updateFile_spec__2(x_18, x_55, x_64, x_65, x_57, x_37, x_54);
lean_dec_ref(x_55);
lean_dec(x_18);
return x_66;
}
}
}
}
else
{
uint8_t x_67; 
lean_dec_ref(x_39);
lean_dec(x_18);
x_67 = !lean_is_exclusive(x_40);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_68 = lean_ctor_get(x_40, 0);
x_69 = lean_io_error_to_string(x_68);
x_70 = 3;
x_71 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_70);
x_72 = lean_array_get_size(x_37);
x_73 = lean_array_push(x_37, x_71);
if (lean_is_scalar(x_38)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_38;
 lean_ctor_set_tag(x_74, 1);
}
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set_tag(x_40, 0);
lean_ctor_set(x_40, 0, x_74);
return x_40;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_75 = lean_ctor_get(x_40, 0);
x_76 = lean_ctor_get(x_40, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_40);
x_77 = lean_io_error_to_string(x_75);
x_78 = 3;
x_79 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set_uint8(x_79, sizeof(void*)*1, x_78);
x_80 = lean_array_get_size(x_37);
x_81 = lean_array_push(x_37, x_79);
if (lean_is_scalar(x_38)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_38;
 lean_ctor_set_tag(x_82, 1);
}
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_76);
return x_83;
}
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_18);
x_94 = lean_ctor_get(x_33, 1);
lean_inc(x_94);
lean_dec_ref(x_33);
x_95 = lean_ctor_get(x_34, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_34, 1);
lean_inc(x_96);
lean_dec_ref(x_34);
x_5 = x_95;
x_6 = x_96;
x_7 = x_94;
goto block_10;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_18);
lean_dec_ref(x_1);
x_97 = lean_ctor_get(x_26, 1);
lean_inc(x_97);
lean_dec_ref(x_26);
x_98 = lean_ctor_get(x_27, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_27, 1);
lean_inc(x_99);
lean_dec_ref(x_27);
x_5 = x_98;
x_6 = x_99;
x_7 = x_97;
goto block_10;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_18);
lean_dec_ref(x_1);
x_100 = lean_ctor_get(x_23, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_23, 1);
lean_inc(x_101);
lean_dec_ref(x_23);
x_102 = lean_io_error_to_string(x_100);
x_103 = 3;
x_104 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set_uint8(x_104, sizeof(void*)*1, x_103);
x_105 = lean_array_get_size(x_3);
x_106 = lean_array_push(x_3, x_104);
x_5 = x_105;
x_6 = x_106;
x_7 = x_101;
goto block_10;
}
}
else
{
uint8_t x_107; 
lean_dec(x_18);
lean_dec_ref(x_1);
x_107 = !lean_is_exclusive(x_21);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_108 = lean_ctor_get(x_21, 0);
x_109 = lean_io_error_to_string(x_108);
x_110 = 3;
x_111 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set_uint8(x_111, sizeof(void*)*1, x_110);
x_112 = lean_array_get_size(x_3);
x_113 = lean_array_push(x_3, x_111);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
lean_ctor_set_tag(x_21, 0);
lean_ctor_set(x_21, 0, x_114);
return x_21;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_115 = lean_ctor_get(x_21, 0);
x_116 = lean_ctor_get(x_21, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_21);
x_117 = lean_io_error_to_string(x_115);
x_118 = 3;
x_119 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set_uint8(x_119, sizeof(void*)*1, x_118);
x_120 = lean_array_get_size(x_3);
x_121 = lean_array_push(x_3, x_119);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_116);
return x_123;
}
}
}
else
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_17);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_125 = lean_ctor_get(x_17, 0);
x_126 = l_Lake_CacheMap_load___closed__0;
x_127 = lean_string_append(x_1, x_126);
x_128 = lean_io_error_to_string(x_125);
x_129 = lean_string_append(x_127, x_128);
lean_dec_ref(x_128);
x_130 = 3;
x_131 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set_uint8(x_131, sizeof(void*)*1, x_130);
x_132 = lean_array_get_size(x_3);
x_133 = lean_array_push(x_3, x_131);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
lean_ctor_set_tag(x_17, 0);
lean_ctor_set(x_17, 0, x_134);
return x_17;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_135 = lean_ctor_get(x_17, 0);
x_136 = lean_ctor_get(x_17, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_17);
x_137 = l_Lake_CacheMap_load___closed__0;
x_138 = lean_string_append(x_1, x_137);
x_139 = lean_io_error_to_string(x_135);
x_140 = lean_string_append(x_138, x_139);
lean_dec_ref(x_139);
x_141 = 3;
x_142 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set_uint8(x_142, sizeof(void*)*1, x_141);
x_143 = lean_array_get_size(x_3);
x_144 = lean_array_push(x_3, x_142);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_136);
return x_146;
}
}
}
else
{
uint8_t x_147; 
lean_dec_ref(x_1);
x_147 = !lean_is_exclusive(x_14);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_148 = lean_ctor_get(x_14, 0);
x_149 = lean_io_error_to_string(x_148);
x_150 = 3;
x_151 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set_uint8(x_151, sizeof(void*)*1, x_150);
x_152 = lean_array_get_size(x_3);
x_153 = lean_array_push(x_3, x_151);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 0, x_154);
return x_14;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_155 = lean_ctor_get(x_14, 0);
x_156 = lean_ctor_get(x_14, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_14);
x_157 = lean_io_error_to_string(x_155);
x_158 = 3;
x_159 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set_uint8(x_159, sizeof(void*)*1, x_158);
x_160 = lean_array_get_size(x_3);
x_161 = lean_array_push(x_3, x_159);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_156);
return x_163;
}
}
}
else
{
uint8_t x_164; 
lean_dec_ref(x_1);
x_164 = !lean_is_exclusive(x_11);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_165 = lean_ctor_get(x_11, 0);
x_166 = lean_io_error_to_string(x_165);
x_167 = 3;
x_168 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set_uint8(x_168, sizeof(void*)*1, x_167);
x_169 = lean_array_get_size(x_3);
x_170 = lean_array_push(x_3, x_168);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
lean_ctor_set_tag(x_11, 0);
lean_ctor_set(x_11, 0, x_171);
return x_11;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_172 = lean_ctor_get(x_11, 0);
x_173 = lean_ctor_get(x_11, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_11);
x_174 = lean_io_error_to_string(x_172);
x_175 = 3;
x_176 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set_uint8(x_176, sizeof(void*)*1, x_175);
x_177 = lean_array_get_size(x_3);
x_178 = lean_array_push(x_3, x_176);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_173);
return x_180;
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_CacheMap_updateFile_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_CacheMap_updateFile_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_updateFile_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_updateFile_spec__2(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_CacheMap_updateFile_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_CacheMap_updateFile_spec__3(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_updateFile_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_updateFile_spec__4(x_1, x_2, x_3, x_7, x_8, x_6);
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
x_5 = l_Lake_CacheMap_updateFile(x_1, x_2, x_3, x_4);
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
LEAN_EXPORT lean_object* l_Lake_CacheMap_writeFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_createParentDirs(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = 1;
x_8 = lean_io_prim_handle_mk(x_1, x_7, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
lean_dec_ref(x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = 1;
x_12 = lean_io_prim_handle_lock(x_9, x_11, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = l_Lake_CacheMap_writeFile___closed__1;
x_15 = l_IO_FS_Handle_putStrLn(x_9, x_14, x_13);
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
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_ctor_get(x_2, 0);
lean_dec(x_21);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_array_get_size(x_20);
x_24 = lean_box(0);
x_25 = lean_nat_dec_lt(x_22, x_23);
if (x_25 == 0)
{
lean_dec(x_23);
lean_dec_ref(x_20);
lean_dec(x_9);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_24);
lean_ctor_set(x_15, 0, x_2);
return x_15;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_23, x_23);
if (x_26 == 0)
{
lean_dec(x_23);
lean_dec_ref(x_20);
lean_dec(x_9);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_24);
lean_ctor_set(x_15, 0, x_2);
return x_15;
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; 
lean_free_object(x_2);
lean_free_object(x_15);
x_27 = 0;
x_28 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_29 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_updateFile_spec__2(x_9, x_20, x_27, x_28, x_24, x_3, x_17);
lean_dec_ref(x_20);
lean_dec(x_9);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
lean_dec(x_2);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_array_get_size(x_30);
x_33 = lean_box(0);
x_34 = lean_nat_dec_lt(x_31, x_32);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_32);
lean_dec_ref(x_30);
lean_dec(x_9);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_3);
lean_ctor_set(x_15, 0, x_35);
return x_15;
}
else
{
uint8_t x_36; 
x_36 = lean_nat_dec_le(x_32, x_32);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_32);
lean_dec_ref(x_30);
lean_dec(x_9);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_3);
lean_ctor_set(x_15, 0, x_37);
return x_15;
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; 
lean_free_object(x_15);
x_38 = 0;
x_39 = lean_usize_of_nat(x_32);
lean_dec(x_32);
x_40 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_updateFile_spec__2(x_9, x_30, x_38, x_39, x_33, x_3, x_17);
lean_dec_ref(x_30);
lean_dec(x_9);
return x_40;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_41 = lean_ctor_get(x_15, 1);
lean_inc(x_41);
lean_dec(x_15);
x_42 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_42);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_43 = x_2;
} else {
 lean_dec_ref(x_2);
 x_43 = lean_box(0);
}
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_array_get_size(x_42);
x_46 = lean_box(0);
x_47 = lean_nat_dec_lt(x_44, x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_45);
lean_dec_ref(x_42);
lean_dec(x_9);
if (lean_is_scalar(x_43)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_43;
}
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_3);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_41);
return x_49;
}
else
{
uint8_t x_50; 
x_50 = lean_nat_dec_le(x_45, x_45);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_45);
lean_dec_ref(x_42);
lean_dec(x_9);
if (lean_is_scalar(x_43)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_43;
}
lean_ctor_set(x_51, 0, x_46);
lean_ctor_set(x_51, 1, x_3);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_41);
return x_52;
}
else
{
size_t x_53; size_t x_54; lean_object* x_55; 
lean_dec(x_43);
x_53 = 0;
x_54 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_55 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_updateFile_spec__2(x_9, x_42, x_53, x_54, x_46, x_3, x_41);
lean_dec_ref(x_42);
lean_dec(x_9);
return x_55;
}
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_9);
lean_dec_ref(x_2);
x_56 = !lean_is_exclusive(x_15);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_15, 0);
x_58 = lean_io_error_to_string(x_57);
x_59 = 3;
x_60 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_59);
x_61 = lean_array_get_size(x_3);
x_62 = lean_array_push(x_3, x_60);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set_tag(x_15, 0);
lean_ctor_set(x_15, 0, x_63);
return x_15;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_64 = lean_ctor_get(x_15, 0);
x_65 = lean_ctor_get(x_15, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_15);
x_66 = lean_io_error_to_string(x_64);
x_67 = 3;
x_68 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set_uint8(x_68, sizeof(void*)*1, x_67);
x_69 = lean_array_get_size(x_3);
x_70 = lean_array_push(x_3, x_68);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_65);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_9);
lean_dec_ref(x_2);
x_73 = !lean_is_exclusive(x_12);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_74 = lean_ctor_get(x_12, 0);
x_75 = lean_io_error_to_string(x_74);
x_76 = 3;
x_77 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set_uint8(x_77, sizeof(void*)*1, x_76);
x_78 = lean_array_get_size(x_3);
x_79 = lean_array_push(x_3, x_77);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_80);
return x_12;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_81 = lean_ctor_get(x_12, 0);
x_82 = lean_ctor_get(x_12, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_12);
x_83 = lean_io_error_to_string(x_81);
x_84 = 3;
x_85 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set_uint8(x_85, sizeof(void*)*1, x_84);
x_86 = lean_array_get_size(x_3);
x_87 = lean_array_push(x_3, x_85);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_82);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec_ref(x_2);
x_90 = !lean_is_exclusive(x_8);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_91 = lean_ctor_get(x_8, 0);
x_92 = l_Lake_CacheMap_load___closed__0;
x_93 = lean_string_append(x_1, x_92);
x_94 = lean_io_error_to_string(x_91);
x_95 = lean_string_append(x_93, x_94);
lean_dec_ref(x_94);
x_96 = 3;
x_97 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set_uint8(x_97, sizeof(void*)*1, x_96);
x_98 = lean_array_get_size(x_3);
x_99 = lean_array_push(x_3, x_97);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
lean_ctor_set_tag(x_8, 0);
lean_ctor_set(x_8, 0, x_100);
return x_8;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_101 = lean_ctor_get(x_8, 0);
x_102 = lean_ctor_get(x_8, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_8);
x_103 = l_Lake_CacheMap_load___closed__0;
x_104 = lean_string_append(x_1, x_103);
x_105 = lean_io_error_to_string(x_101);
x_106 = lean_string_append(x_104, x_105);
lean_dec_ref(x_105);
x_107 = 3;
x_108 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set_uint8(x_108, sizeof(void*)*1, x_107);
x_109 = lean_array_get_size(x_3);
x_110 = lean_array_push(x_3, x_108);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_102);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_113 = !lean_is_exclusive(x_5);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_114 = lean_ctor_get(x_5, 0);
x_115 = lean_io_error_to_string(x_114);
x_116 = 3;
x_117 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set_uint8(x_117, sizeof(void*)*1, x_116);
x_118 = lean_array_get_size(x_3);
x_119 = lean_array_push(x_3, x_117);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_120);
return x_5;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_121 = lean_ctor_get(x_5, 0);
x_122 = lean_ctor_get(x_5, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_5);
x_123 = lean_io_error_to_string(x_121);
x_124 = 3;
x_125 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set_uint8(x_125, sizeof(void*)*1, x_124);
x_126 = lean_array_get_size(x_3);
x_127 = lean_array_push(x_3, x_125);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_122);
return x_129;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lake_CacheMap_get_x3f_spec__0_spec__0___redArg(uint64_t x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lake_CacheMap_get_x3f_spec__0_spec__0(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lake_CacheMap_get_x3f_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lake_CacheMap_get_x3f_spec__0___redArg(lean_object* x_1, uint64_t x_2) {
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
x_17 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lake_CacheMap_get_x3f_spec__0_spec__0___redArg(x_2, x_16);
lean_dec(x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lake_CacheMap_get_x3f_spec__0(lean_object* x_1, lean_object* x_2, uint64_t x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lake_CacheMap_get_x3f_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_get_x3f(uint64_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lake_CacheMap_get_x3f_spec__0___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lake_CacheMap_get_x3f_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lake_CacheMap_get_x3f_spec__0_spec__0___redArg(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lake_CacheMap_get_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lake_CacheMap_get_x3f_spec__0_spec__0(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lake_CacheMap_get_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lake_CacheMap_get_x3f_spec__0___redArg(x_1, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lake_CacheMap_get_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_5 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lake_CacheMap_get_x3f_spec__0(x_1, x_2, x_4);
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
x_4 = l_Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___redArg(x_3, x_1, x_2);
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
x_6 = l_Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___redArg(x_4, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_apply_1(x_2, x_4);
x_7 = l_Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___redArg(x_5, x_3, x_6);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
x_8 = lean_array_uget(x_1, x_2);
x_9 = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(x_4, x_8, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
x_4 = x_12;
x_5 = x_13;
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_6);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at_____private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 4);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = l_Std_DTreeMap_Internal_Impl_foldlM___at_____private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1(x_1, x_6, x_3, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(x_11, x_5, x_12, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_1 = x_16;
x_2 = x_7;
x_3 = x_17;
x_4 = x_15;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_3);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_4);
return x_20;
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
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
case 1:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get_uint8(x_2, 0);
lean_dec_ref(x_2);
x_8 = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__0;
if (x_7 == 0)
{
lean_object* x_17; 
x_17 = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__1;
x_9 = x_17;
goto block_16;
}
else
{
lean_object* x_18; 
x_18 = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__2;
x_9 = x_18;
goto block_16;
}
block_16:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_string_append(x_8, x_9);
lean_dec_ref(x_9);
x_11 = 3;
x_12 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_11);
x_13 = lean_array_push(x_3, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
}
case 2:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_19);
lean_dec_ref(x_2);
x_20 = l_Lake_Hash_ofJsonNumber_x3f(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__3;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__1;
x_25 = lean_string_append(x_23, x_24);
x_26 = l_Lean_JsonNumber_toString(x_19);
x_27 = lean_string_append(x_25, x_26);
lean_dec_ref(x_26);
x_28 = 3;
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
x_30 = lean_array_push(x_3, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_4);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint64_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec_ref(x_19);
x_33 = lean_ctor_get(x_20, 0);
lean_inc(x_33);
lean_dec_ref(x_20);
x_34 = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__4;
x_35 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_unbox_uint64(x_33);
lean_dec(x_33);
lean_ctor_set_uint64(x_35, sizeof(void*)*1, x_36);
x_37 = lean_array_push(x_1, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_3);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_4);
return x_39;
}
}
case 3:
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_40);
lean_dec_ref(x_2);
x_41 = l_Lake_ArtifactDescr_ofFilePath_x3f(x_40);
lean_dec_ref(x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__0;
x_44 = lean_string_append(x_43, x_42);
lean_dec(x_42);
x_45 = 3;
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_45);
x_47 = lean_array_push(x_3, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_4);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_41, 0);
lean_inc(x_50);
lean_dec_ref(x_41);
x_51 = lean_array_push(x_1, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_3);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_4);
return x_53;
}
}
case 4:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_54);
lean_dec_ref(x_2);
x_55 = lean_unsigned_to_nat(0u);
x_56 = lean_array_get_size(x_54);
x_57 = lean_nat_dec_lt(x_55, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_56);
lean_dec_ref(x_54);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_1);
lean_ctor_set(x_58, 1, x_3);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_4);
return x_59;
}
else
{
uint8_t x_60; 
x_60 = lean_nat_dec_le(x_56, x_56);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_56);
lean_dec_ref(x_54);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_1);
lean_ctor_set(x_61, 1, x_3);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_4);
return x_62;
}
else
{
size_t x_63; size_t x_64; lean_object* x_65; 
x_63 = 0;
x_64 = lean_usize_of_nat(x_56);
lean_dec(x_56);
x_65 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0(x_54, x_63, x_64, x_1, x_3, x_4);
lean_dec_ref(x_54);
return x_65;
}
}
}
default: 
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_2, 0);
lean_inc(x_66);
lean_dec_ref(x_2);
x_67 = l_Std_DTreeMap_Internal_Impl_foldlM___at_____private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1(x_1, x_66, x_3, x_4);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_CacheMap_collectOutputDescrs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
lean_dec_ref(x_2);
x_9 = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(x_1, x_7, x_3, x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_1 = x_12;
x_2 = x_8;
x_3 = x_13;
x_4 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_collectOutputDescrs_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
x_8 = lean_array_uget(x_1, x_2);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_CacheMap_collectOutputDescrs_spec__0(x_4, x_8, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
x_4 = x_12;
x_5 = x_13;
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_6);
return x_18;
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
LEAN_EXPORT lean_object* l_Lake_CacheMap_collectOutputDescrs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_18; uint8_t x_19; 
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
x_18 = lean_array_get_size(x_4);
x_19 = lean_nat_dec_lt(x_6, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_18);
lean_dec_ref(x_4);
lean_inc_ref(x_2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_2);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_3);
x_9 = x_21;
x_10 = x_2;
x_11 = x_3;
goto block_17;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_18, x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_18);
lean_dec_ref(x_4);
lean_inc_ref(x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_7);
lean_ctor_set(x_23, 1, x_2);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_3);
x_9 = x_24;
x_10 = x_2;
x_11 = x_3;
goto block_17;
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = 0;
x_26 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_27 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_collectOutputDescrs_spec__1(x_4, x_25, x_26, x_7, x_2, x_3);
lean_dec_ref(x_4);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_9 = x_27;
x_10 = x_30;
x_11 = x_29;
goto block_17;
}
}
block_17:
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
lean_object* x_15; lean_object* x_16; 
lean_dec_ref(x_9);
if (lean_is_scalar(x_5)) {
 x_15 = lean_alloc_ctor(1, 2, 0);
} else {
 x_15 = x_5;
 lean_ctor_set_tag(x_15, 1);
}
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_collectOutputDescrs_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_collectOutputDescrs_spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_mk(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_st_mk_ref(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_get_x3f(uint64_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
lean_inc(x_5);
x_7 = lean_st_ref_set(x_2, x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_dec(x_9);
x_10 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lake_CacheMap_get_x3f_spec__0___redArg(x_5, x_1);
lean_dec(x_5);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lake_CacheMap_get_x3f_spec__0___redArg(x_5, x_1);
lean_dec(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_get_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_5 = l_Lake_CacheRef_get_x3f(x_4, x_2, x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___redArg(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_st_ref_take(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_apply_1(x_1, x_3);
x_10 = l_Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___redArg(x_7, x_2, x_9);
x_11 = lean_st_ref_set(x_4, x_10, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_st_ref_take(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_apply_1(x_2, x_4);
x_11 = l_Std_DHashMap_Internal_Raw_u2080_insert___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__2___redArg(x_8, x_3, x_10);
x_12 = lean_st_ref_set(x_5, x_11, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint64_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_7 = l_Lake_CacheRef_insert___redArg(x_1, x_6, x_3, x_4, x_5);
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
x_8 = l_Lake_CacheRef_insert(x_1, x_2, x_7, x_4, x_5, x_6);
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
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_4 = lean_ctor_get_uint64(x_2, sizeof(void*)*1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = l_Lake_Cache_artifactDir___closed__0;
x_7 = l_System_FilePath_join(x_1, x_6);
x_43 = lean_string_utf8_byte_size(x_5);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_nat_dec_eq(x_43, x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = l_Lake_Hash_hex(x_4);
x_47 = l_Lake_Cache_artifactPath___closed__0;
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_string_append(x_48, x_5);
x_8 = x_49;
goto block_42;
}
else
{
lean_object* x_50; 
x_50 = l_Lake_Hash_hex(x_4);
x_8 = x_50;
goto block_42;
}
block_42:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_System_FilePath_join(x_7, x_8);
lean_dec_ref(x_8);
x_10 = lean_io_metadata(x_9, x_3);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
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
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_18);
lean_dec(x_16);
lean_inc_ref(x_9);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_9);
lean_ctor_set(x_19, 2, x_9);
lean_ctor_set(x_19, 3, x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_dec_ref(x_10);
x_23 = l_System_FilePath_pathExists(x_9, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
uint8_t x_26; 
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_23, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_23, 0, x_28);
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_23, 0);
lean_dec(x_33);
x_34 = l_Lake_Cache_getArtifact_x3f___closed__1;
lean_inc_ref(x_9);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_2);
lean_ctor_set(x_35, 1, x_9);
lean_ctor_set(x_35, 2, x_9);
lean_ctor_set(x_35, 3, x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_23, 0, x_36);
return x_23;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_23, 1);
lean_inc(x_37);
lean_dec(x_23);
x_38 = l_Lake_Cache_getArtifact_x3f___closed__1;
lean_inc_ref(x_9);
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_2);
lean_ctor_set(x_39, 1, x_9);
lean_ctor_set(x_39, 2, x_9);
lean_ctor_set(x_39, 3, x_38);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
}
}
}
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
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_4 = lean_ctor_get_uint64(x_2, sizeof(void*)*1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = l_Lake_Cache_artifactDir___closed__0;
x_7 = l_System_FilePath_join(x_1, x_6);
x_41 = lean_string_utf8_byte_size(x_5);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_nat_dec_eq(x_41, x_42);
lean_dec(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = l_Lake_Hash_hex(x_4);
x_45 = l_Lake_Cache_artifactPath___closed__0;
x_46 = lean_string_append(x_44, x_45);
x_47 = lean_string_append(x_46, x_5);
x_8 = x_47;
goto block_40;
}
else
{
lean_object* x_48; 
x_48 = l_Lake_Hash_hex(x_4);
x_8 = x_48;
goto block_40;
}
block_40:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_System_FilePath_join(x_7, x_8);
lean_dec_ref(x_8);
x_10 = lean_io_metadata(x_9, x_3);
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_17);
lean_dec(x_15);
lean_inc_ref(x_9);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_9);
lean_ctor_set(x_18, 2, x_9);
lean_ctor_set(x_18, 3, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec_ref(x_10);
x_21 = l_System_FilePath_pathExists(x_9, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
uint8_t x_24; 
lean_dec_ref(x_2);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
x_26 = l_Lake_Cache_getArtifact___closed__0;
x_27 = lean_string_append(x_26, x_9);
lean_dec_ref(x_9);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 0, x_27);
return x_21;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_dec(x_21);
x_29 = l_Lake_Cache_getArtifact___closed__0;
x_30 = lean_string_append(x_29, x_9);
lean_dec_ref(x_9);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_21);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_21, 0);
lean_dec(x_33);
x_34 = l_Lake_Cache_getArtifact_x3f___closed__1;
lean_inc_ref(x_9);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_2);
lean_ctor_set(x_35, 1, x_9);
lean_ctor_set(x_35, 2, x_9);
lean_ctor_set(x_35, 3, x_34);
lean_ctor_set(x_21, 0, x_35);
return x_21;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_21, 1);
lean_inc(x_36);
lean_dec(x_21);
x_37 = l_Lake_Cache_getArtifact_x3f___closed__1;
lean_inc_ref(x_9);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_2);
lean_ctor_set(x_38, 1, x_9);
lean_ctor_set(x_38, 2, x_9);
lean_ctor_set(x_38, 3, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___Lake_Cache_getArtifactPaths_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_4, x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec_ref(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_array_fget_borrowed(x_3, x_4);
lean_inc_ref(x_2);
lean_inc(x_11);
x_12 = lean_apply_3(x_2, x_11, x_6, x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec_ref(x_13);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_4, x_17);
lean_dec(x_4);
x_19 = lean_array_push(x_5, x_15);
x_4 = x_18;
x_5 = x_19;
x_6 = x_16;
x_7 = x_14;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_12, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_12;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_12, 0, x_26);
return x_12;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_dec(x_12);
x_28 = lean_ctor_get(x_13, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_13, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_30 = x_13;
} else {
 lean_dec_ref(x_13);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(1, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___Lake_Cache_getArtifactPaths_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___Lake_Cache_getArtifactPaths_spec__0___redArg(x_3, x_4, x_5, x_6, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifactPaths___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_11 = lean_ctor_get_uint64(x_2, sizeof(void*)*1);
x_12 = lean_ctor_get(x_2, 0);
x_13 = l_Lake_Cache_artifactDir___closed__0;
x_14 = l_System_FilePath_join(x_1, x_13);
x_28 = lean_string_utf8_byte_size(x_12);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_nat_dec_eq(x_28, x_29);
lean_dec(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = l_Lake_Hash_hex(x_11);
x_32 = l_Lake_Cache_artifactPath___closed__0;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_string_append(x_33, x_12);
x_15 = x_34;
goto block_27;
}
else
{
lean_object* x_35; 
x_35 = l_Lake_Hash_hex(x_11);
x_15 = x_35;
goto block_27;
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
block_27:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = l_System_FilePath_join(x_14, x_15);
lean_dec_ref(x_15);
x_17 = l_System_FilePath_pathExists(x_16, x_4);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec_ref(x_17);
x_21 = l_Lake_Cache_getArtifact___closed__0;
x_22 = lean_string_append(x_21, x_16);
x_23 = 3;
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_23);
x_25 = lean_array_push(x_3, x_24);
x_5 = x_16;
x_6 = x_25;
x_7 = x_20;
goto block_10;
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_dec_ref(x_17);
x_5 = x_16;
x_6 = x_3;
x_7 = x_26;
goto block_10;
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
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifactPaths(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_alloc_closure((void*)(l_Lake_Cache_getArtifactPaths___lam__0___boxed), 4, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_array_get_size(x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lake_Cache_getArtifactPaths___closed__0;
lean_inc_ref(x_3);
x_9 = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___Lake_Cache_getArtifactPaths_spec__0___redArg(x_6, x_5, x_2, x_7, x_8, x_3, x_4);
lean_dec(x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = lean_array_get_size(x_3);
lean_dec_ref(x_3);
x_16 = lean_array_get_size(x_13);
x_17 = lean_nat_dec_eq(x_15, x_16);
lean_dec(x_16);
x_18 = l_instDecidableNot___redArg(x_17);
if (x_18 == 0)
{
lean_dec(x_15);
lean_free_object(x_10);
lean_dec(x_13);
lean_dec(x_11);
return x_9;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_9, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_9, 0);
lean_dec(x_21);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_15);
return x_9;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_15);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_11);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_dec(x_10);
x_24 = lean_array_get_size(x_3);
lean_dec_ref(x_3);
x_25 = lean_array_get_size(x_23);
x_26 = lean_nat_dec_eq(x_24, x_25);
lean_dec(x_25);
x_27 = l_instDecidableNot___redArg(x_26);
if (x_27 == 0)
{
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_11);
return x_9;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_28 = x_9;
} else {
 lean_dec_ref(x_9);
 x_28 = lean_box(0);
}
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_23);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_11);
return x_30;
}
}
}
else
{
lean_dec_ref(x_10);
lean_dec_ref(x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___Lake_Cache_getArtifactPaths_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___Lake_Cache_getArtifactPaths_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___Lake_Cache_getArtifactPaths_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___Lake_Cache_getArtifactPaths_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_5);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifactPaths___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Cache_getArtifactPaths___lam__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifactPaths___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Cache_getArtifactPaths(x_1, x_2, x_3, x_4);
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
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputsCore(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_13 = l_Lake_createParentDirs(x_12, x_5);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = l_Lean_Json_compress(x_4);
x_16 = l_IO_FS_writeFile(x_12, x_15, x_14);
lean_dec_ref(x_15);
lean_dec_ref(x_12);
return x_16;
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
x_7 = l_Lake_Cache_writeOutputsCore(x_1, x_2, x_6, x_4, x_5);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint64_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_apply_1(x_1, x_5);
x_8 = l_Lake_Cache_writeOutputsCore(x_2, x_3, x_4, x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint64_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_apply_1(x_2, x_6);
x_9 = l_Lake_Cache_writeOutputsCore(x_3, x_4, x_5, x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint64_t x_7; lean_object* x_8; 
x_7 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_8 = l_Lake_Cache_writeOutputs___redArg(x_1, x_2, x_3, x_7, x_5, x_6);
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
x_9 = l_Lake_Cache_writeOutputs(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
lean_dec_ref(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_Cache_writeMap_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; 
lean_dec_ref(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
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
x_11 = l_Lake_Cache_writeOutputsCore(x_1, x_2, x_10, x_8, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_3 = x_12;
x_4 = x_9;
x_5 = x_13;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Cache_writeMap_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
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
x_11 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_Cache_writeMap_spec__0(x_1, x_2, x_10, x_9, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = 1;
x_15 = lean_usize_add(x_4, x_14);
x_4 = x_15;
x_6 = x_12;
x_7 = x_13;
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
lean_object* x_17; 
lean_dec_ref(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_7);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeMap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_get_size(x_6);
x_10 = lean_box(0);
x_11 = lean_nat_dec_lt(x_8, x_9);
if (x_11 == 0)
{
lean_dec(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_9, x_9);
if (x_12 == 0)
{
lean_dec(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; 
lean_free_object(x_3);
x_13 = 0;
x_14 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Cache_writeMap_spec__1(x_1, x_2, x_6, x_13, x_14, x_10, x_4);
lean_dec_ref(x_6);
return x_15;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get_size(x_16);
x_19 = lean_box(0);
x_20 = lean_nat_dec_lt(x_17, x_18);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_18);
lean_dec_ref(x_16);
lean_dec_ref(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_4);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_18, x_18);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_18);
lean_dec_ref(x_16);
lean_dec_ref(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_4);
return x_23;
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; 
x_24 = 0;
x_25 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_26 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Cache_writeMap_spec__1(x_1, x_2, x_16, x_24, x_25, x_19, x_4);
lean_dec_ref(x_16);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_Cache_writeMap_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lake_Cache_writeMap_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Cache_writeMap_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_Cache_writeMap_spec__1(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeMap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Cache_writeMap(x_1, x_2, x_3, x_4);
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
LEAN_EXPORT lean_object* l_Lake_Cache_readOutputs_x3f(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_13 = l_IO_FS_readFile(x_12, x_5);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lean_Json_parse(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Lake_Cache_readOutputs_x3f___closed__0;
x_19 = lean_string_append(x_12, x_18);
x_20 = lean_string_append(x_19, x_17);
lean_dec(x_17);
x_21 = 2;
x_22 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_21);
x_23 = lean_array_push(x_4, x_22);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_13, 0, x_25);
return x_13;
}
else
{
uint8_t x_26; 
lean_dec_ref(x_12);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_4);
lean_ctor_set(x_13, 0, x_27);
return x_13;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_16, 0);
lean_inc(x_28);
lean_dec(x_16);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_4);
lean_ctor_set(x_13, 0, x_30);
return x_13;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_13, 0);
x_32 = lean_ctor_get(x_13, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_13);
x_33 = l_Lean_Json_parse(x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = l_Lake_Cache_readOutputs_x3f___closed__0;
x_36 = lean_string_append(x_12, x_35);
x_37 = lean_string_append(x_36, x_34);
lean_dec(x_34);
x_38 = 2;
x_39 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_38);
x_40 = lean_array_push(x_4, x_39);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_32);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec_ref(x_12);
x_44 = lean_ctor_get(x_33, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 x_45 = x_33;
} else {
 lean_dec_ref(x_33);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 1, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_44);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_4);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_32);
return x_48;
}
}
}
else
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_13, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 11)
{
uint8_t x_50; 
lean_dec_ref(x_49);
lean_dec_ref(x_12);
x_50 = !lean_is_exclusive(x_13);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_13, 0);
lean_dec(x_51);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_4);
lean_ctor_set_tag(x_13, 0);
lean_ctor_set(x_13, 0, x_53);
return x_13;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_13, 1);
lean_inc(x_54);
lean_dec(x_13);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_4);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
return x_57;
}
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_13);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_59 = lean_ctor_get(x_13, 0);
lean_dec(x_59);
x_60 = l_Lake_Cache_readOutputs_x3f___closed__1;
x_61 = lean_string_append(x_12, x_60);
x_62 = lean_io_error_to_string(x_49);
x_63 = lean_string_append(x_61, x_62);
lean_dec_ref(x_62);
x_64 = 3;
x_65 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_64);
x_66 = lean_array_get_size(x_4);
x_67 = lean_array_push(x_4, x_65);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set_tag(x_13, 0);
lean_ctor_set(x_13, 0, x_68);
return x_13;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_69 = lean_ctor_get(x_13, 1);
lean_inc(x_69);
lean_dec(x_13);
x_70 = l_Lake_Cache_readOutputs_x3f___closed__1;
x_71 = lean_string_append(x_12, x_70);
x_72 = lean_io_error_to_string(x_49);
x_73 = lean_string_append(x_71, x_72);
lean_dec_ref(x_72);
x_74 = 3;
x_75 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set_uint8(x_75, sizeof(void*)*1, x_74);
x_76 = lean_array_get_size(x_4);
x_77 = lean_array_push(x_4, x_75);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_69);
return x_79;
}
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
x_7 = l_Lake_Cache_readOutputs_x3f(x_1, x_2, x_6, x_4, x_5);
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
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
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
x_34 = l_Lake_proc(x_33, x_31, x_30, x_6);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_37 = lean_ctor_get(x_34, 1);
x_38 = lean_ctor_get(x_34, 0);
lean_dec(x_38);
x_39 = lean_ctor_get(x_35, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_dec_ref(x_35);
x_41 = lean_array_get_size(x_40);
x_42 = lean_nat_dec_lt(x_29, x_41);
if (x_42 == 0)
{
lean_dec(x_41);
lean_dec(x_40);
lean_dec_ref(x_5);
lean_ctor_set(x_34, 0, x_39);
return x_34;
}
else
{
uint8_t x_43; 
x_43 = lean_nat_dec_le(x_41, x_41);
if (x_43 == 0)
{
lean_dec(x_41);
lean_dec(x_40);
lean_dec_ref(x_5);
lean_ctor_set(x_34, 0, x_39);
return x_34;
}
else
{
lean_object* x_44; size_t x_45; size_t x_46; lean_object* x_47; uint8_t x_48; 
lean_free_object(x_34);
x_44 = lean_box(0);
x_45 = 0;
x_46 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_47 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0(x_40, x_45, x_46, x_44, x_5, x_37);
lean_dec(x_40);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
lean_ctor_set(x_47, 0, x_39);
return x_47;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_39);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_34, 1);
lean_inc(x_52);
lean_dec(x_34);
x_53 = lean_ctor_get(x_35, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_35, 1);
lean_inc(x_54);
lean_dec_ref(x_35);
x_55 = lean_array_get_size(x_54);
x_56 = lean_nat_dec_lt(x_29, x_55);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_5);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_52);
return x_57;
}
else
{
uint8_t x_58; 
x_58 = lean_nat_dec_le(x_55, x_55);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_5);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_52);
return x_59;
}
else
{
lean_object* x_60; size_t x_61; size_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_box(0);
x_61 = 0;
x_62 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_63 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0(x_54, x_61, x_62, x_60, x_5, x_52);
lean_dec(x_54);
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
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_53);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_34);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_68 = lean_ctor_get(x_34, 1);
x_69 = lean_ctor_get(x_34, 0);
lean_dec(x_69);
x_70 = lean_ctor_get(x_35, 1);
lean_inc(x_70);
lean_dec_ref(x_35);
x_71 = lean_array_get_size(x_70);
x_72 = lean_nat_dec_lt(x_29, x_71);
if (x_72 == 0)
{
lean_object* x_73; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_5);
x_73 = lean_box(0);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 0, x_73);
return x_34;
}
else
{
uint8_t x_74; 
lean_free_object(x_34);
x_74 = lean_nat_dec_le(x_71, x_71);
if (x_74 == 0)
{
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_5);
x_7 = x_68;
goto block_10;
}
else
{
lean_object* x_75; size_t x_76; size_t x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_box(0);
x_76 = 0;
x_77 = lean_usize_of_nat(x_71);
lean_dec(x_71);
x_78 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0(x_70, x_76, x_77, x_75, x_5, x_68);
lean_dec(x_70);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec_ref(x_78);
x_7 = x_79;
goto block_10;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_80 = lean_ctor_get(x_34, 1);
lean_inc(x_80);
lean_dec(x_34);
x_81 = lean_ctor_get(x_35, 1);
lean_inc(x_81);
lean_dec_ref(x_35);
x_82 = lean_array_get_size(x_81);
x_83 = lean_nat_dec_lt(x_29, x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_82);
lean_dec(x_81);
lean_dec_ref(x_5);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_80);
return x_85;
}
else
{
uint8_t x_86; 
x_86 = lean_nat_dec_le(x_82, x_82);
if (x_86 == 0)
{
lean_dec(x_82);
lean_dec(x_81);
lean_dec_ref(x_5);
x_7 = x_80;
goto block_10;
}
else
{
lean_object* x_87; size_t x_88; size_t x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_box(0);
x_88 = 0;
x_89 = lean_usize_of_nat(x_82);
lean_dec(x_82);
x_90 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0(x_81, x_88, x_89, x_87, x_5, x_80);
lean_dec(x_81);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec_ref(x_90);
x_7 = x_91;
goto block_10;
}
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Config_Cache_0__Lake_uploadS3(x_1, x_2, x_3, x_4, x_5, x_6);
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
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at_____private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_String_split___at_____private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_box(0);
x_4 = l_String_splitAux___at___String_split___at_____private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0_spec__0(x_1, x_2, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_____private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_3; lean_object* x_4; 
x_3 = l_String_split___at_____private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0(x_2);
x_4 = l_List_foldl___at_____private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__2(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at_____private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_splitAux___at___String_split___at_____private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_split___at_____private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_split___at_____private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_____private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at_____private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__2(x_1, x_2);
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
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint64_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_13 = lean_ctor_get(x_1, 0);
x_86 = l_Lake_CacheService_artifactUrl(x_12, x_3, x_4);
x_149 = l_Lake_Cache_artifactDir___closed__0;
x_150 = l_System_FilePath_join(x_2, x_149);
x_168 = lean_string_utf8_byte_size(x_13);
x_169 = lean_unsigned_to_nat(0u);
x_170 = lean_nat_dec_eq(x_168, x_169);
lean_dec(x_168);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_171 = l_Lake_Hash_hex(x_12);
x_172 = l_Lake_Cache_artifactPath___closed__0;
x_173 = lean_string_append(x_171, x_172);
x_174 = lean_string_append(x_173, x_13);
x_151 = x_174;
goto block_167;
}
else
{
lean_object* x_175; 
x_175 = l_Lake_Hash_hex(x_12);
x_151 = x_175;
goto block_167;
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
block_85:
{
lean_object* x_16; 
x_16 = l_Lake_computeBinFileHash(x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint64_t x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_unbox_uint64(x_18);
lean_dec(x_18);
x_21 = lean_uint64_dec_eq(x_20, x_12);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_free_object(x_16);
x_22 = l_Lake_CacheService_downloadArtifact___closed__0;
lean_inc_ref(x_14);
x_23 = lean_string_append(x_14, x_22);
x_24 = 3;
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
lean_inc_ref(x_6);
x_26 = lean_apply_2(x_6, x_25, x_19);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_io_remove_file(x_14, x_27);
lean_dec_ref(x_14);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
lean_dec_ref(x_6);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_35 = lean_ctor_get(x_28, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_28, 1);
lean_inc(x_36);
lean_dec_ref(x_28);
x_37 = lean_io_error_to_string(x_35);
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_24);
x_39 = lean_apply_2(x_6, x_38, x_36);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = lean_box(0);
lean_ctor_set_tag(x_39, 1);
lean_ctor_set(x_39, 0, x_42);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
lean_object* x_46; 
lean_dec_ref(x_14);
lean_dec_ref(x_6);
x_46 = lean_box(0);
lean_ctor_set(x_16, 0, x_46);
return x_16;
}
}
else
{
lean_object* x_47; lean_object* x_48; uint64_t x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_16, 0);
x_48 = lean_ctor_get(x_16, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_16);
x_49 = lean_unbox_uint64(x_47);
lean_dec(x_47);
x_50 = lean_uint64_dec_eq(x_49, x_12);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_51 = l_Lake_CacheService_downloadArtifact___closed__0;
lean_inc_ref(x_14);
x_52 = lean_string_append(x_14, x_51);
x_53 = 3;
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_53);
lean_inc_ref(x_6);
x_55 = lean_apply_2(x_6, x_54, x_48);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = lean_io_remove_file(x_14, x_56);
lean_dec_ref(x_14);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec_ref(x_6);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
x_60 = lean_box(0);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_59;
 lean_ctor_set_tag(x_61, 1);
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_62 = lean_ctor_get(x_57, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
lean_dec_ref(x_57);
x_64 = lean_io_error_to_string(x_62);
x_65 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_53);
x_66 = lean_apply_2(x_6, x_65, x_63);
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
x_69 = lean_box(0);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_68;
 lean_ctor_set_tag(x_70, 1);
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec_ref(x_14);
lean_dec_ref(x_6);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_48);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec_ref(x_14);
x_73 = lean_ctor_get(x_16, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_16, 1);
lean_inc(x_74);
lean_dec_ref(x_16);
x_75 = lean_io_error_to_string(x_73);
x_76 = 3;
x_77 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set_uint8(x_77, sizeof(void*)*1, x_76);
x_78 = lean_apply_2(x_6, x_77, x_74);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_78, 0);
lean_dec(x_80);
x_81 = lean_box(0);
lean_ctor_set_tag(x_78, 1);
lean_ctor_set(x_78, 0, x_81);
return x_78;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_78, 1);
lean_inc(x_82);
lean_dec(x_78);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
}
block_142:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_89 = l_Lake_CacheService_downloadArtifact___closed__1;
x_90 = lean_string_append(x_4, x_89);
x_91 = l_Lake_Hash_hex(x_12);
x_92 = lean_string_append(x_90, x_91);
lean_dec_ref(x_91);
x_93 = l_Lake_CacheService_downloadArtifact___closed__2;
x_94 = lean_string_append(x_92, x_93);
x_95 = lean_string_append(x_94, x_87);
x_96 = l_Lake_CacheService_downloadArtifact___closed__3;
x_97 = lean_string_append(x_95, x_96);
x_98 = lean_string_append(x_97, x_86);
x_99 = 1;
x_100 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set_uint8(x_100, sizeof(void*)*1, x_99);
lean_inc_ref(x_6);
x_101 = lean_apply_2(x_6, x_100, x_88);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec_ref(x_101);
x_103 = lean_unsigned_to_nat(0u);
x_104 = l_Lake_Cache_getArtifactPaths___closed__0;
lean_inc_ref(x_87);
x_105 = l_Lake_download(x_86, x_87, x_104, x_104, x_102);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec_ref(x_105);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec_ref(x_106);
x_109 = lean_array_get_size(x_108);
x_110 = lean_nat_dec_lt(x_103, x_109);
if (x_110 == 0)
{
lean_dec(x_109);
lean_dec(x_108);
x_14 = x_87;
x_15 = x_107;
goto block_85;
}
else
{
uint8_t x_111; 
x_111 = lean_nat_dec_le(x_109, x_109);
if (x_111 == 0)
{
lean_dec(x_109);
lean_dec(x_108);
x_14 = x_87;
x_15 = x_107;
goto block_85;
}
else
{
lean_object* x_112; size_t x_113; size_t x_114; lean_object* x_115; lean_object* x_116; 
x_112 = lean_box(0);
x_113 = 0;
x_114 = lean_usize_of_nat(x_109);
lean_dec(x_109);
lean_inc_ref(x_6);
x_115 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0(x_108, x_113, x_114, x_112, x_6, x_107);
lean_dec(x_108);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
lean_dec_ref(x_115);
x_14 = x_87;
x_15 = x_116;
goto block_85;
}
}
}
else
{
uint8_t x_117; 
lean_dec_ref(x_87);
x_117 = !lean_is_exclusive(x_105);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_118 = lean_ctor_get(x_105, 1);
x_119 = lean_ctor_get(x_105, 0);
lean_dec(x_119);
x_120 = lean_ctor_get(x_106, 1);
lean_inc(x_120);
lean_dec_ref(x_106);
x_121 = lean_array_get_size(x_120);
x_122 = lean_nat_dec_lt(x_103, x_121);
if (x_122 == 0)
{
lean_object* x_123; 
lean_dec(x_121);
lean_dec(x_120);
lean_dec_ref(x_6);
x_123 = lean_box(0);
lean_ctor_set_tag(x_105, 1);
lean_ctor_set(x_105, 0, x_123);
return x_105;
}
else
{
uint8_t x_124; 
lean_free_object(x_105);
x_124 = lean_nat_dec_le(x_121, x_121);
if (x_124 == 0)
{
lean_dec(x_121);
lean_dec(x_120);
lean_dec_ref(x_6);
x_8 = x_118;
goto block_11;
}
else
{
lean_object* x_125; size_t x_126; size_t x_127; lean_object* x_128; lean_object* x_129; 
x_125 = lean_box(0);
x_126 = 0;
x_127 = lean_usize_of_nat(x_121);
lean_dec(x_121);
x_128 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0(x_120, x_126, x_127, x_125, x_6, x_118);
lean_dec(x_120);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec_ref(x_128);
x_8 = x_129;
goto block_11;
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_130 = lean_ctor_get(x_105, 1);
lean_inc(x_130);
lean_dec(x_105);
x_131 = lean_ctor_get(x_106, 1);
lean_inc(x_131);
lean_dec_ref(x_106);
x_132 = lean_array_get_size(x_131);
x_133 = lean_nat_dec_lt(x_103, x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_132);
lean_dec(x_131);
lean_dec_ref(x_6);
x_134 = lean_box(0);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_130);
return x_135;
}
else
{
uint8_t x_136; 
x_136 = lean_nat_dec_le(x_132, x_132);
if (x_136 == 0)
{
lean_dec(x_132);
lean_dec(x_131);
lean_dec_ref(x_6);
x_8 = x_130;
goto block_11;
}
else
{
lean_object* x_137; size_t x_138; size_t x_139; lean_object* x_140; lean_object* x_141; 
x_137 = lean_box(0);
x_138 = 0;
x_139 = lean_usize_of_nat(x_132);
lean_dec(x_132);
x_140 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0(x_131, x_138, x_139, x_137, x_6, x_130);
lean_dec(x_131);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec_ref(x_140);
x_8 = x_141;
goto block_11;
}
}
}
}
}
block_148:
{
if (x_144 == 0)
{
x_87 = x_143;
x_88 = x_145;
goto block_142;
}
else
{
if (x_5 == 0)
{
lean_object* x_146; lean_object* x_147; 
lean_dec_ref(x_143);
lean_dec_ref(x_86);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
x_146 = lean_box(0);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
else
{
x_87 = x_143;
x_88 = x_145;
goto block_142;
}
}
}
block_167:
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_152 = l_System_FilePath_join(x_150, x_151);
lean_dec_ref(x_151);
x_153 = l_System_FilePath_pathExists(x_152, x_7);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec_ref(x_153);
x_156 = l_Lake_CacheMap_parse___closed__5;
x_157 = l_Lake_CacheService_downloadArtifact___closed__5;
if (x_157 == 0)
{
uint8_t x_158; 
x_158 = lean_unbox(x_154);
lean_dec(x_154);
x_143 = x_152;
x_144 = x_158;
x_145 = x_155;
goto block_148;
}
else
{
uint8_t x_159; 
x_159 = l_Lake_CacheService_downloadArtifact___closed__6;
if (x_159 == 0)
{
uint8_t x_160; 
x_160 = lean_unbox(x_154);
lean_dec(x_154);
x_143 = x_152;
x_144 = x_160;
x_145 = x_155;
goto block_148;
}
else
{
lean_object* x_161; size_t x_162; size_t x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_161 = lean_box(0);
x_162 = 0;
x_163 = l_Lake_CacheService_downloadArtifact___closed__7;
lean_inc_ref(x_6);
x_164 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0(x_156, x_162, x_163, x_161, x_6, x_155);
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec_ref(x_164);
x_166 = lean_unbox(x_154);
lean_dec(x_154);
x_143 = x_152;
x_144 = x_166;
x_145 = x_165;
goto block_148;
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
x_9 = l_Lake_CacheService_downloadArtifact(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact___at___Lake_CacheService_downloadArtifacts___elam__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint64_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_12 = lean_ctor_get_uint64(x_2, sizeof(void*)*1);
x_13 = lean_ctor_get(x_2, 0);
x_86 = l_Lake_CacheService_artifactUrl(x_12, x_4, x_5);
x_149 = l_Lake_Cache_artifactDir___closed__0;
x_150 = l_System_FilePath_join(x_3, x_149);
x_168 = lean_string_utf8_byte_size(x_13);
x_169 = lean_unsigned_to_nat(0u);
x_170 = lean_nat_dec_eq(x_168, x_169);
lean_dec(x_168);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_171 = l_Lake_Hash_hex(x_12);
x_172 = l_Lake_Cache_artifactPath___closed__0;
x_173 = lean_string_append(x_171, x_172);
x_174 = lean_string_append(x_173, x_13);
x_151 = x_174;
goto block_167;
}
else
{
lean_object* x_175; 
x_175 = l_Lake_Hash_hex(x_12);
x_151 = x_175;
goto block_167;
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
block_85:
{
lean_object* x_16; 
x_16 = l_Lake_computeBinFileHash(x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint64_t x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_unbox_uint64(x_18);
lean_dec(x_18);
x_21 = lean_uint64_dec_eq(x_20, x_12);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_free_object(x_16);
x_22 = l_Lake_CacheService_downloadArtifact___closed__0;
lean_inc_ref(x_14);
x_23 = lean_string_append(x_14, x_22);
x_24 = 3;
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
lean_inc_ref(x_1);
x_26 = lean_apply_2(x_1, x_25, x_19);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_io_remove_file(x_14, x_27);
lean_dec_ref(x_14);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
lean_dec_ref(x_1);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_35 = lean_ctor_get(x_28, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_28, 1);
lean_inc(x_36);
lean_dec_ref(x_28);
x_37 = lean_io_error_to_string(x_35);
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_24);
x_39 = lean_apply_2(x_1, x_38, x_36);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = lean_box(0);
lean_ctor_set_tag(x_39, 1);
lean_ctor_set(x_39, 0, x_42);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
lean_object* x_46; 
lean_dec_ref(x_14);
lean_dec_ref(x_1);
x_46 = lean_box(0);
lean_ctor_set(x_16, 0, x_46);
return x_16;
}
}
else
{
lean_object* x_47; lean_object* x_48; uint64_t x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_16, 0);
x_48 = lean_ctor_get(x_16, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_16);
x_49 = lean_unbox_uint64(x_47);
lean_dec(x_47);
x_50 = lean_uint64_dec_eq(x_49, x_12);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_51 = l_Lake_CacheService_downloadArtifact___closed__0;
lean_inc_ref(x_14);
x_52 = lean_string_append(x_14, x_51);
x_53 = 3;
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_53);
lean_inc_ref(x_1);
x_55 = lean_apply_2(x_1, x_54, x_48);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = lean_io_remove_file(x_14, x_56);
lean_dec_ref(x_14);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec_ref(x_1);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
x_60 = lean_box(0);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_59;
 lean_ctor_set_tag(x_61, 1);
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_62 = lean_ctor_get(x_57, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
lean_dec_ref(x_57);
x_64 = lean_io_error_to_string(x_62);
x_65 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_53);
x_66 = lean_apply_2(x_1, x_65, x_63);
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
x_69 = lean_box(0);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_68;
 lean_ctor_set_tag(x_70, 1);
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec_ref(x_14);
lean_dec_ref(x_1);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_48);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec_ref(x_14);
x_73 = lean_ctor_get(x_16, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_16, 1);
lean_inc(x_74);
lean_dec_ref(x_16);
x_75 = lean_io_error_to_string(x_73);
x_76 = 3;
x_77 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set_uint8(x_77, sizeof(void*)*1, x_76);
x_78 = lean_apply_2(x_1, x_77, x_74);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_78, 0);
lean_dec(x_80);
x_81 = lean_box(0);
lean_ctor_set_tag(x_78, 1);
lean_ctor_set(x_78, 0, x_81);
return x_78;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_78, 1);
lean_inc(x_82);
lean_dec(x_78);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
}
block_142:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_89 = l_Lake_CacheService_downloadArtifact___closed__1;
x_90 = lean_string_append(x_5, x_89);
x_91 = l_Lake_Hash_hex(x_12);
x_92 = lean_string_append(x_90, x_91);
lean_dec_ref(x_91);
x_93 = l_Lake_CacheService_downloadArtifact___closed__2;
x_94 = lean_string_append(x_92, x_93);
x_95 = lean_string_append(x_94, x_88);
x_96 = l_Lake_CacheService_downloadArtifact___closed__3;
x_97 = lean_string_append(x_95, x_96);
x_98 = lean_string_append(x_97, x_86);
x_99 = 1;
x_100 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set_uint8(x_100, sizeof(void*)*1, x_99);
lean_inc_ref(x_1);
x_101 = lean_apply_2(x_1, x_100, x_87);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec_ref(x_101);
x_103 = lean_unsigned_to_nat(0u);
x_104 = l_Lake_Cache_getArtifactPaths___closed__0;
lean_inc_ref(x_88);
x_105 = l_Lake_download(x_86, x_88, x_104, x_104, x_102);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec_ref(x_105);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec_ref(x_106);
x_109 = lean_array_get_size(x_108);
x_110 = lean_nat_dec_lt(x_103, x_109);
if (x_110 == 0)
{
lean_dec(x_109);
lean_dec(x_108);
x_14 = x_88;
x_15 = x_107;
goto block_85;
}
else
{
uint8_t x_111; 
x_111 = lean_nat_dec_le(x_109, x_109);
if (x_111 == 0)
{
lean_dec(x_109);
lean_dec(x_108);
x_14 = x_88;
x_15 = x_107;
goto block_85;
}
else
{
lean_object* x_112; size_t x_113; size_t x_114; lean_object* x_115; lean_object* x_116; 
x_112 = lean_box(0);
x_113 = 0;
x_114 = lean_usize_of_nat(x_109);
lean_dec(x_109);
lean_inc_ref(x_1);
x_115 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0(x_108, x_113, x_114, x_112, x_1, x_107);
lean_dec(x_108);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
lean_dec_ref(x_115);
x_14 = x_88;
x_15 = x_116;
goto block_85;
}
}
}
else
{
uint8_t x_117; 
lean_dec_ref(x_88);
x_117 = !lean_is_exclusive(x_105);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_118 = lean_ctor_get(x_105, 1);
x_119 = lean_ctor_get(x_105, 0);
lean_dec(x_119);
x_120 = lean_ctor_get(x_106, 1);
lean_inc(x_120);
lean_dec_ref(x_106);
x_121 = lean_array_get_size(x_120);
x_122 = lean_nat_dec_lt(x_103, x_121);
if (x_122 == 0)
{
lean_object* x_123; 
lean_dec(x_121);
lean_dec(x_120);
lean_dec_ref(x_1);
x_123 = lean_box(0);
lean_ctor_set_tag(x_105, 1);
lean_ctor_set(x_105, 0, x_123);
return x_105;
}
else
{
uint8_t x_124; 
lean_free_object(x_105);
x_124 = lean_nat_dec_le(x_121, x_121);
if (x_124 == 0)
{
lean_dec(x_121);
lean_dec(x_120);
lean_dec_ref(x_1);
x_8 = x_118;
goto block_11;
}
else
{
lean_object* x_125; size_t x_126; size_t x_127; lean_object* x_128; lean_object* x_129; 
x_125 = lean_box(0);
x_126 = 0;
x_127 = lean_usize_of_nat(x_121);
lean_dec(x_121);
x_128 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0(x_120, x_126, x_127, x_125, x_1, x_118);
lean_dec(x_120);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec_ref(x_128);
x_8 = x_129;
goto block_11;
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_130 = lean_ctor_get(x_105, 1);
lean_inc(x_130);
lean_dec(x_105);
x_131 = lean_ctor_get(x_106, 1);
lean_inc(x_131);
lean_dec_ref(x_106);
x_132 = lean_array_get_size(x_131);
x_133 = lean_nat_dec_lt(x_103, x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_132);
lean_dec(x_131);
lean_dec_ref(x_1);
x_134 = lean_box(0);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_130);
return x_135;
}
else
{
uint8_t x_136; 
x_136 = lean_nat_dec_le(x_132, x_132);
if (x_136 == 0)
{
lean_dec(x_132);
lean_dec(x_131);
lean_dec_ref(x_1);
x_8 = x_130;
goto block_11;
}
else
{
lean_object* x_137; size_t x_138; size_t x_139; lean_object* x_140; lean_object* x_141; 
x_137 = lean_box(0);
x_138 = 0;
x_139 = lean_usize_of_nat(x_132);
lean_dec(x_132);
x_140 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0(x_131, x_138, x_139, x_137, x_1, x_130);
lean_dec(x_131);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec_ref(x_140);
x_8 = x_141;
goto block_11;
}
}
}
}
}
block_148:
{
if (x_144 == 0)
{
x_87 = x_145;
x_88 = x_143;
goto block_142;
}
else
{
if (x_6 == 0)
{
lean_object* x_146; lean_object* x_147; 
lean_dec_ref(x_143);
lean_dec_ref(x_86);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_146 = lean_box(0);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
else
{
x_87 = x_145;
x_88 = x_143;
goto block_142;
}
}
}
block_167:
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_152 = l_System_FilePath_join(x_150, x_151);
lean_dec_ref(x_151);
x_153 = l_System_FilePath_pathExists(x_152, x_7);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec_ref(x_153);
x_156 = l_Lake_CacheMap_parse___closed__5;
x_157 = l_Lake_CacheService_downloadArtifact___closed__5;
if (x_157 == 0)
{
uint8_t x_158; 
x_158 = lean_unbox(x_154);
lean_dec(x_154);
x_143 = x_152;
x_144 = x_158;
x_145 = x_155;
goto block_148;
}
else
{
uint8_t x_159; 
x_159 = l_Lake_CacheService_downloadArtifact___closed__6;
if (x_159 == 0)
{
uint8_t x_160; 
x_160 = lean_unbox(x_154);
lean_dec(x_154);
x_143 = x_152;
x_144 = x_160;
x_145 = x_155;
goto block_148;
}
else
{
lean_object* x_161; size_t x_162; size_t x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_161 = lean_box(0);
x_162 = 0;
x_163 = l_Lake_CacheService_downloadArtifact___closed__7;
lean_inc_ref(x_1);
x_164 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0(x_156, x_162, x_163, x_161, x_1, x_155);
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec_ref(x_164);
x_166 = lean_unbox(x_154);
lean_dec(x_154);
x_143 = x_152;
x_144 = x_166;
x_145 = x_165;
goto block_148;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___elam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_CacheService_downloadArtifact___at___Lake_CacheService_downloadArtifacts___elam__0_spec__0(x_7, x_6, x_1, x_2, x_3, x_4, x_8);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_box(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_9, 0);
lean_dec(x_17);
x_18 = 0;
x_19 = lean_box(x_18);
lean_ctor_set_tag(x_9, 0);
lean_ctor_set(x_9, 0, x_19);
return x_9;
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
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
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___elam__0___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheService_downloadArtifacts_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_CacheService_downloadArtifact___at___Lake_CacheService_downloadArtifacts___elam__0_spec__0(x_1, x_7, x_2, x_3, x_4, x_5, x_8);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_box(x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_9, 0);
lean_dec(x_17);
x_18 = 0;
x_19 = lean_box(x_18);
lean_ctor_set_tag(x_9, 0);
lean_ctor_set(x_9, 0, x_19);
return x_9;
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheService_downloadArtifacts_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, size_t x_6, size_t x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_6, x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; uint8_t x_18; 
x_12 = lean_array_uget(x_5, x_6);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
lean_inc_ref(x_9);
x_13 = l_Lake_CacheService_downloadArtifacts___elam__0___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheService_downloadArtifacts_spec__0_spec__0(x_9, x_1, x_2, x_3, x_4, x_8, x_12, x_10);
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = 1;
x_17 = lean_usize_add(x_6, x_16);
x_18 = lean_unbox(x_14);
lean_dec(x_14);
x_6 = x_17;
x_8 = x_18;
x_10 = x_15;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_9);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_20 = lean_box(x_8);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_10);
return x_21;
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
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
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
x_8 = x_7;
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
x_8 = x_7;
goto block_11;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_13);
lean_dec(x_13);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheService_downloadArtifacts_spec__0(x_2, x_3, x_4, x_5, x_1, x_16, x_17, x_15, x_6, x_7);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec_ref(x_18);
x_22 = l_Lake_CacheService_downloadArtifacts___closed__0;
x_23 = lean_string_append(x_4, x_22);
x_24 = 3;
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
x_26 = lean_apply_2(x_6, x_25, x_21);
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
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; 
lean_dec_ref(x_6);
lean_dec_ref(x_4);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_dec_ref(x_18);
x_8 = x_33;
goto block_11;
}
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact___at___Lake_CacheService_downloadArtifacts___elam__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_6);
x_9 = l_Lake_CacheService_downloadArtifact___at___Lake_CacheService_downloadArtifacts___elam__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_8, x_7);
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
x_11 = l_Lake_CacheService_downloadArtifacts___elam__0(x_1, x_2, x_3, x_9, x_10, x_6, x_7, x_8);
lean_dec_ref(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___elam__0___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheService_downloadArtifacts_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_5);
x_10 = lean_unbox(x_6);
x_11 = l_Lake_CacheService_downloadArtifacts___elam__0___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheService_downloadArtifacts_spec__0_spec__0(x_1, x_2, x_3, x_4, x_9, x_10, x_7, x_8);
lean_dec_ref(x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheService_downloadArtifacts_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; uint8_t x_14; lean_object* x_15; 
x_11 = lean_unbox(x_4);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_14 = lean_unbox(x_8);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheService_downloadArtifacts_spec__0(x_1, x_2, x_3, x_11, x_5, x_12, x_13, x_14, x_9, x_10);
lean_dec_ref(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
x_9 = l_Lake_CacheService_downloadArtifacts(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___at___Lake_CacheService_downloadOutputArtifacts_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
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
x_8 = x_7;
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
x_8 = x_7;
goto block_11;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_13);
lean_dec(x_13);
lean_inc_ref(x_1);
lean_inc_ref(x_5);
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheService_downloadArtifacts_spec__0(x_3, x_4, x_5, x_6, x_2, x_16, x_17, x_15, x_1, x_7);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec_ref(x_18);
x_22 = l_Lake_CacheService_downloadArtifacts___closed__0;
x_23 = lean_string_append(x_5, x_22);
x_24 = 3;
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
x_26 = lean_apply_2(x_1, x_25, x_21);
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
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; 
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_dec_ref(x_18);
x_8 = x_33;
goto block_11;
}
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadOutputArtifacts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_13; 
lean_inc_ref(x_1);
lean_inc_ref(x_2);
x_13 = l_Lake_Cache_writeMap(x_2, x_4, x_1, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lake_CacheMap_parse___closed__5;
x_17 = l_Lake_CacheMap_collectOutputDescrs(x_1, x_16, x_14);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec_ref(x_18);
x_22 = lean_array_get_size(x_21);
x_23 = lean_nat_dec_lt(x_15, x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_22);
lean_dec(x_21);
x_24 = l_Lake_CacheService_downloadArtifacts___at___Lake_CacheService_downloadOutputArtifacts_spec__0(x_7, x_20, x_2, x_3, x_5, x_6, x_19);
lean_dec(x_20);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_22, x_22);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_21);
x_26 = l_Lake_CacheService_downloadArtifacts___at___Lake_CacheService_downloadOutputArtifacts_spec__0(x_7, x_20, x_2, x_3, x_5, x_6, x_19);
lean_dec(x_20);
return x_26;
}
else
{
lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_box(0);
x_28 = 0;
x_29 = lean_usize_of_nat(x_22);
lean_dec(x_22);
lean_inc_ref(x_7);
x_30 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0(x_21, x_28, x_29, x_27, x_7, x_19);
lean_dec(x_21);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = l_Lake_CacheService_downloadArtifacts___at___Lake_CacheService_downloadOutputArtifacts_spec__0(x_7, x_20, x_2, x_3, x_5, x_6, x_31);
lean_dec(x_20);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_33 = !lean_is_exclusive(x_17);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_17, 1);
x_35 = lean_ctor_get(x_17, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_18, 1);
lean_inc(x_36);
lean_dec_ref(x_18);
x_37 = lean_array_get_size(x_36);
x_38 = lean_nat_dec_lt(x_15, x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec_ref(x_7);
x_39 = lean_box(0);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_39);
return x_17;
}
else
{
uint8_t x_40; 
lean_free_object(x_17);
x_40 = lean_nat_dec_le(x_37, x_37);
if (x_40 == 0)
{
lean_dec(x_37);
lean_dec(x_36);
lean_dec_ref(x_7);
x_9 = x_34;
goto block_12;
}
else
{
lean_object* x_41; size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_box(0);
x_42 = 0;
x_43 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_44 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0(x_36, x_42, x_43, x_41, x_7, x_34);
lean_dec(x_36);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec_ref(x_44);
x_9 = x_45;
goto block_12;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_17, 1);
lean_inc(x_46);
lean_dec(x_17);
x_47 = lean_ctor_get(x_18, 1);
lean_inc(x_47);
lean_dec_ref(x_18);
x_48 = lean_array_get_size(x_47);
x_49 = lean_nat_dec_lt(x_15, x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_48);
lean_dec(x_47);
lean_dec_ref(x_7);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_46);
return x_51;
}
else
{
uint8_t x_52; 
x_52 = lean_nat_dec_le(x_48, x_48);
if (x_52 == 0)
{
lean_dec(x_48);
lean_dec(x_47);
lean_dec_ref(x_7);
x_9 = x_46;
goto block_12;
}
else
{
lean_object* x_53; size_t x_54; size_t x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_box(0);
x_54 = 0;
x_55 = lean_usize_of_nat(x_48);
lean_dec(x_48);
x_56 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0(x_47, x_54, x_55, x_53, x_7, x_46);
lean_dec(x_47);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec_ref(x_56);
x_9 = x_57;
goto block_12;
}
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_58 = lean_ctor_get(x_13, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_13, 1);
lean_inc(x_59);
lean_dec_ref(x_13);
x_60 = lean_io_error_to_string(x_58);
x_61 = 3;
x_62 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_61);
x_63 = lean_apply_2(x_7, x_62, x_59);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_63, 0);
lean_dec(x_65);
x_66 = lean_box(0);
lean_ctor_set_tag(x_63, 1);
lean_ctor_set(x_63, 0, x_66);
return x_63;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_dec(x_63);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___at___Lake_CacheService_downloadOutputArtifacts_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_6);
x_9 = l_Lake_CacheService_downloadArtifacts___at___Lake_CacheService_downloadOutputArtifacts_spec__0(x_1, x_2, x_3, x_4, x_5, x_8, x_7);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadOutputArtifacts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_6);
x_10 = l_Lake_CacheService_downloadOutputArtifacts(x_1, x_2, x_3, x_4, x_5, x_9, x_7, x_8);
lean_dec_ref(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___at___Lake_CacheService_uploadArtifact_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
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
x_34 = l_Lake_proc(x_33, x_31, x_30, x_6);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_37 = lean_ctor_get(x_34, 1);
x_38 = lean_ctor_get(x_34, 0);
lean_dec(x_38);
x_39 = lean_ctor_get(x_35, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_dec_ref(x_35);
x_41 = lean_array_get_size(x_40);
x_42 = lean_nat_dec_lt(x_29, x_41);
if (x_42 == 0)
{
lean_dec(x_41);
lean_dec(x_40);
lean_dec_ref(x_1);
lean_ctor_set(x_34, 0, x_39);
return x_34;
}
else
{
uint8_t x_43; 
x_43 = lean_nat_dec_le(x_41, x_41);
if (x_43 == 0)
{
lean_dec(x_41);
lean_dec(x_40);
lean_dec_ref(x_1);
lean_ctor_set(x_34, 0, x_39);
return x_34;
}
else
{
lean_object* x_44; size_t x_45; size_t x_46; lean_object* x_47; uint8_t x_48; 
lean_free_object(x_34);
x_44 = lean_box(0);
x_45 = 0;
x_46 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_47 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0(x_40, x_45, x_46, x_44, x_1, x_37);
lean_dec(x_40);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
lean_ctor_set(x_47, 0, x_39);
return x_47;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_39);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_34, 1);
lean_inc(x_52);
lean_dec(x_34);
x_53 = lean_ctor_get(x_35, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_35, 1);
lean_inc(x_54);
lean_dec_ref(x_35);
x_55 = lean_array_get_size(x_54);
x_56 = lean_nat_dec_lt(x_29, x_55);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_1);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_52);
return x_57;
}
else
{
uint8_t x_58; 
x_58 = lean_nat_dec_le(x_55, x_55);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_1);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_52);
return x_59;
}
else
{
lean_object* x_60; size_t x_61; size_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_box(0);
x_61 = 0;
x_62 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_63 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0(x_54, x_61, x_62, x_60, x_1, x_52);
lean_dec(x_54);
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
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_53);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_34);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_68 = lean_ctor_get(x_34, 1);
x_69 = lean_ctor_get(x_34, 0);
lean_dec(x_69);
x_70 = lean_ctor_get(x_35, 1);
lean_inc(x_70);
lean_dec_ref(x_35);
x_71 = lean_array_get_size(x_70);
x_72 = lean_nat_dec_lt(x_29, x_71);
if (x_72 == 0)
{
lean_object* x_73; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_73 = lean_box(0);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 0, x_73);
return x_34;
}
else
{
uint8_t x_74; 
lean_free_object(x_34);
x_74 = lean_nat_dec_le(x_71, x_71);
if (x_74 == 0)
{
lean_dec(x_71);
lean_dec(x_70);
lean_dec_ref(x_1);
x_7 = x_68;
goto block_10;
}
else
{
lean_object* x_75; size_t x_76; size_t x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_box(0);
x_76 = 0;
x_77 = lean_usize_of_nat(x_71);
lean_dec(x_71);
x_78 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0(x_70, x_76, x_77, x_75, x_1, x_68);
lean_dec(x_70);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec_ref(x_78);
x_7 = x_79;
goto block_10;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_80 = lean_ctor_get(x_34, 1);
lean_inc(x_80);
lean_dec(x_34);
x_81 = lean_ctor_get(x_35, 1);
lean_inc(x_81);
lean_dec_ref(x_35);
x_82 = lean_array_get_size(x_81);
x_83 = lean_nat_dec_lt(x_29, x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_82);
lean_dec(x_81);
lean_dec_ref(x_1);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_80);
return x_85;
}
else
{
uint8_t x_86; 
x_86 = lean_nat_dec_le(x_82, x_82);
if (x_86 == 0)
{
lean_dec(x_82);
lean_dec(x_81);
lean_dec_ref(x_1);
x_7 = x_80;
goto block_10;
}
else
{
lean_object* x_87; size_t x_88; size_t x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_box(0);
x_88 = 0;
x_89 = lean_usize_of_nat(x_82);
lean_dec(x_82);
x_90 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0(x_81, x_88, x_89, x_87, x_1, x_80);
lean_dec(x_81);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec_ref(x_90);
x_7 = x_91;
goto block_10;
}
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
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
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact(uint64_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
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
x_20 = lean_apply_2(x_5, x_19, x_6);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_22);
lean_dec_ref(x_3);
x_23 = l_Lake_CacheService_artifactContentType___closed__0;
x_24 = l___private_Lake_Config_Cache_0__Lake_uploadS3___at___Lake_CacheService_uploadArtifact_spec__0(x_5, x_2, x_23, x_7, x_22, x_21);
return x_24;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___at___Lake_CacheService_uploadArtifact_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Config_Cache_0__Lake_uploadS3___at___Lake_CacheService_uploadArtifact_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_8 = l_Lake_CacheService_uploadArtifact(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact___at___Lake_CacheService_uploadArtifacts___elam__0_spec__0(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
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
x_20 = lean_apply_2(x_1, x_19, x_6);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_22);
lean_dec_ref(x_4);
x_23 = l_Lake_CacheService_artifactContentType___closed__0;
x_24 = l___private_Lake_Config_Cache_0__Lake_uploadS3___at___Lake_CacheService_uploadArtifact_spec__0(x_1, x_3, x_23, x_7, x_22, x_21);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint64_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_fget_borrowed(x_1, x_5);
x_9 = lean_ctor_get_uint64(x_8, sizeof(void*)*1);
x_10 = lean_array_fget_borrowed(x_2, x_5);
lean_inc_ref(x_10);
x_11 = l_Lake_CacheService_uploadArtifact___at___Lake_CacheService_uploadArtifacts___elam__0_spec__0(x_6, x_9, x_10, x_3, x_4, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_CacheService_uploadArtifacts___elam__0___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___at_____private_Init_Data_Nat_Control_0__Nat_forM_loop___at___Lake_CacheService_uploadArtifacts_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint64_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_fget_borrowed(x_2, x_6);
x_9 = lean_ctor_get_uint64(x_8, sizeof(void*)*1);
x_10 = lean_array_fget_borrowed(x_3, x_6);
lean_inc_ref(x_10);
x_11 = l_Lake_CacheService_uploadArtifact___at___Lake_CacheService_uploadArtifacts___elam__0_spec__0(x_1, x_9, x_10, x_4, x_5, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___at_____private_Init_Data_Nat_Control_0__Nat_forM_loop___at___Lake_CacheService_uploadArtifacts_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_CacheService_uploadArtifacts___elam__0___at_____private_Init_Data_Nat_Control_0__Nat_forM_loop___at___Lake_CacheService_uploadArtifacts_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___Lake_CacheService_uploadArtifacts_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
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
x_17 = l_Lake_CacheService_uploadArtifacts___elam__0___at_____private_Init_Data_Nat_Control_0__Nat_forM_loop___at___Lake_CacheService_uploadArtifacts_spec__0_spec__0___redArg(x_7, x_1, x_2, x_3, x_4, x_16, x_8);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec_ref(x_17);
x_6 = x_14;
x_8 = x_18;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___Lake_CacheService_uploadArtifacts_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___Lake_CacheService_uploadArtifacts_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___Lake_CacheService_uploadArtifacts_spec__0___redArg(x_2, x_3, x_4, x_5, x_1, x_1, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact___at___Lake_CacheService_uploadArtifacts___elam__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint64_t x_7; lean_object* x_8; 
x_7 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_8 = l_Lake_CacheService_uploadArtifact___at___Lake_CacheService_uploadArtifacts___elam__0_spec__0(x_1, x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_CacheService_uploadArtifacts___elam__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
x_9 = l_Lake_CacheService_uploadArtifacts___elam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___at_____private_Init_Data_Nat_Control_0__Nat_forM_loop___at___Lake_CacheService_uploadArtifacts_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_CacheService_uploadArtifacts___elam__0___at_____private_Init_Data_Nat_Control_0__Nat_forM_loop___at___Lake_CacheService_uploadArtifacts_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___elam__0___at_____private_Init_Data_Nat_Control_0__Nat_forM_loop___at___Lake_CacheService_uploadArtifacts_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_CacheService_uploadArtifacts___elam__0___at_____private_Init_Data_Nat_Control_0__Nat_forM_loop___at___Lake_CacheService_uploadArtifacts_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___Lake_CacheService_uploadArtifacts_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___Lake_CacheService_uploadArtifacts_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___Lake_CacheService_uploadArtifacts_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___Lake_CacheService_uploadArtifacts_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_8 = l_Lake_CacheService_uploadArtifacts(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_20; lean_object* x_24; lean_object* x_25; lean_object* x_29; lean_object* x_30; lean_object* x_41; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_154; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_220; uint8_t x_221; 
x_44 = l_Lake_Cache_revisionDir___closed__0;
x_45 = l_System_FilePath_join(x_2, x_44);
x_46 = l_System_FilePath_join(x_45, x_1);
x_47 = l_Lake_Cache_revisionPath___closed__0;
lean_inc_ref(x_4);
x_48 = lean_string_append(x_4, x_47);
x_49 = l_System_FilePath_join(x_46, x_48);
lean_dec_ref(x_48);
x_174 = l_System_FilePath_pathExists(x_49, x_10);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec_ref(x_174);
x_220 = l_Lake_CacheMap_parse___closed__5;
x_221 = l_Lake_CacheService_downloadArtifact___closed__5;
if (x_221 == 0)
{
x_177 = x_176;
goto block_219;
}
else
{
uint8_t x_222; 
x_222 = l_Lake_CacheService_downloadArtifact___closed__6;
if (x_222 == 0)
{
x_177 = x_176;
goto block_219;
}
else
{
lean_object* x_223; size_t x_224; size_t x_225; lean_object* x_226; lean_object* x_227; 
x_223 = lean_box(0);
x_224 = 0;
x_225 = l_Lake_CacheService_downloadArtifact___closed__7;
lean_inc_ref(x_9);
x_226 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0(x_220, x_224, x_225, x_223, x_9, x_176);
x_227 = lean_ctor_get(x_226, 1);
lean_inc(x_227);
lean_dec_ref(x_226);
x_177 = x_227;
goto block_219;
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
block_19:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
block_23:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
block_28:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
block_40:
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_31 = l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__0;
x_32 = lean_string_append(x_5, x_31);
x_33 = 3;
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_33);
x_35 = lean_apply_2(x_9, x_34, x_30);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 0, x_29);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_29);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
block_43:
{
lean_object* x_42; 
x_42 = lean_box(0);
x_29 = x_42;
x_30 = x_41;
goto block_40;
}
block_123:
{
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec_ref(x_49);
lean_dec_ref(x_9);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_50, 0);
lean_inc(x_54);
lean_dec_ref(x_50);
x_55 = l_Lake_createParentDirs(x_49, x_51);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = l_IO_FS_writeFile(x_49, x_54, x_56);
lean_dec(x_54);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec_ref(x_57);
x_59 = lean_unsigned_to_nat(0u);
x_60 = l_Lake_CacheMap_parse___closed__5;
x_61 = l_Lake_CacheMap_load(x_49, x_60, x_58);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec_ref(x_61);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec_ref(x_62);
x_66 = lean_array_get_size(x_65);
x_67 = lean_nat_dec_lt(x_59, x_66);
if (x_67 == 0)
{
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_9);
x_24 = x_64;
x_25 = x_63;
goto block_28;
}
else
{
uint8_t x_68; 
x_68 = lean_nat_dec_le(x_66, x_66);
if (x_68 == 0)
{
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_9);
x_24 = x_64;
x_25 = x_63;
goto block_28;
}
else
{
lean_object* x_69; size_t x_70; size_t x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_box(0);
x_70 = 0;
x_71 = lean_usize_of_nat(x_66);
lean_dec(x_66);
x_72 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0(x_65, x_70, x_71, x_69, x_9, x_63);
lean_dec(x_65);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec_ref(x_72);
x_24 = x_64;
x_25 = x_73;
goto block_28;
}
}
}
else
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_61);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_75 = lean_ctor_get(x_61, 1);
x_76 = lean_ctor_get(x_61, 0);
lean_dec(x_76);
x_77 = lean_ctor_get(x_62, 1);
lean_inc(x_77);
lean_dec_ref(x_62);
x_78 = lean_array_get_size(x_77);
x_79 = lean_nat_dec_lt(x_59, x_78);
if (x_79 == 0)
{
lean_object* x_80; 
lean_dec(x_78);
lean_dec(x_77);
lean_dec_ref(x_9);
x_80 = lean_box(0);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 0, x_80);
return x_61;
}
else
{
uint8_t x_81; 
lean_free_object(x_61);
x_81 = lean_nat_dec_le(x_78, x_78);
if (x_81 == 0)
{
lean_dec(x_78);
lean_dec(x_77);
lean_dec_ref(x_9);
x_20 = x_75;
goto block_23;
}
else
{
lean_object* x_82; size_t x_83; size_t x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_box(0);
x_83 = 0;
x_84 = lean_usize_of_nat(x_78);
lean_dec(x_78);
x_85 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0(x_77, x_83, x_84, x_82, x_9, x_75);
lean_dec(x_77);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec_ref(x_85);
x_20 = x_86;
goto block_23;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_87 = lean_ctor_get(x_61, 1);
lean_inc(x_87);
lean_dec(x_61);
x_88 = lean_ctor_get(x_62, 1);
lean_inc(x_88);
lean_dec_ref(x_62);
x_89 = lean_array_get_size(x_88);
x_90 = lean_nat_dec_lt(x_59, x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_89);
lean_dec(x_88);
lean_dec_ref(x_9);
x_91 = lean_box(0);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_87);
return x_92;
}
else
{
uint8_t x_93; 
x_93 = lean_nat_dec_le(x_89, x_89);
if (x_93 == 0)
{
lean_dec(x_89);
lean_dec(x_88);
lean_dec_ref(x_9);
x_20 = x_87;
goto block_23;
}
else
{
lean_object* x_94; size_t x_95; size_t x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_box(0);
x_95 = 0;
x_96 = lean_usize_of_nat(x_89);
lean_dec(x_89);
x_97 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0(x_88, x_95, x_96, x_94, x_9, x_87);
lean_dec(x_88);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec_ref(x_97);
x_20 = x_98;
goto block_23;
}
}
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
lean_dec_ref(x_49);
x_99 = lean_ctor_get(x_57, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_57, 1);
lean_inc(x_100);
lean_dec_ref(x_57);
x_101 = lean_io_error_to_string(x_99);
x_102 = 3;
x_103 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set_uint8(x_103, sizeof(void*)*1, x_102);
x_104 = lean_apply_2(x_9, x_103, x_100);
x_105 = !lean_is_exclusive(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_104, 0);
lean_dec(x_106);
x_107 = lean_box(0);
lean_ctor_set_tag(x_104, 1);
lean_ctor_set(x_104, 0, x_107);
return x_104;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_104, 1);
lean_inc(x_108);
lean_dec(x_104);
x_109 = lean_box(0);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
lean_dec(x_54);
lean_dec_ref(x_49);
x_111 = lean_ctor_get(x_55, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_55, 1);
lean_inc(x_112);
lean_dec_ref(x_55);
x_113 = lean_io_error_to_string(x_111);
x_114 = 3;
x_115 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set_uint8(x_115, sizeof(void*)*1, x_114);
x_116 = lean_apply_2(x_9, x_115, x_112);
x_117 = !lean_is_exclusive(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_116, 0);
lean_dec(x_118);
x_119 = lean_box(0);
lean_ctor_set_tag(x_116, 1);
lean_ctor_set(x_116, 0, x_119);
return x_116;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_116, 1);
lean_inc(x_120);
lean_dec(x_116);
x_121 = lean_box(0);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
}
}
block_153:
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_unsigned_to_nat(0u);
x_128 = l_Lake_CacheMap_parse___closed__5;
x_129 = l_Lake_getUrl_x3f(x_124, x_126, x_128, x_125);
lean_dec_ref(x_126);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
lean_dec_ref(x_5);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec_ref(x_129);
x_132 = lean_ctor_get(x_130, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
lean_dec_ref(x_130);
x_134 = lean_array_get_size(x_133);
x_135 = lean_nat_dec_lt(x_127, x_134);
if (x_135 == 0)
{
lean_dec(x_134);
lean_dec(x_133);
x_50 = x_132;
x_51 = x_131;
goto block_123;
}
else
{
uint8_t x_136; 
x_136 = lean_nat_dec_le(x_134, x_134);
if (x_136 == 0)
{
lean_dec(x_134);
lean_dec(x_133);
x_50 = x_132;
x_51 = x_131;
goto block_123;
}
else
{
lean_object* x_137; size_t x_138; size_t x_139; lean_object* x_140; lean_object* x_141; 
x_137 = lean_box(0);
x_138 = 0;
x_139 = lean_usize_of_nat(x_134);
lean_dec(x_134);
lean_inc_ref(x_9);
x_140 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0(x_133, x_138, x_139, x_137, x_9, x_131);
lean_dec(x_133);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec_ref(x_140);
x_50 = x_132;
x_51 = x_141;
goto block_123;
}
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
lean_dec_ref(x_49);
x_142 = lean_ctor_get(x_129, 1);
lean_inc(x_142);
lean_dec_ref(x_129);
x_143 = lean_ctor_get(x_130, 1);
lean_inc(x_143);
lean_dec_ref(x_130);
x_144 = lean_array_get_size(x_143);
x_145 = lean_nat_dec_lt(x_127, x_144);
if (x_145 == 0)
{
lean_object* x_146; 
lean_dec(x_144);
lean_dec(x_143);
x_146 = lean_box(0);
x_29 = x_146;
x_30 = x_142;
goto block_40;
}
else
{
uint8_t x_147; 
x_147 = lean_nat_dec_le(x_144, x_144);
if (x_147 == 0)
{
lean_dec(x_144);
lean_dec(x_143);
x_41 = x_142;
goto block_43;
}
else
{
lean_object* x_148; size_t x_149; size_t x_150; lean_object* x_151; lean_object* x_152; 
x_148 = lean_box(0);
x_149 = 0;
x_150 = lean_usize_of_nat(x_144);
lean_dec(x_144);
lean_inc_ref(x_9);
x_151 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0(x_143, x_149, x_150, x_148, x_9, x_142);
lean_dec(x_143);
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
lean_dec_ref(x_151);
x_41 = x_152;
goto block_43;
}
}
}
}
block_173:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
lean_inc_ref(x_3);
x_155 = l_Lake_CacheService_revisionUrl(x_1, x_3, x_5, x_6, x_7);
x_156 = l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__1;
x_157 = lean_string_append(x_4, x_156);
x_158 = lean_string_append(x_157, x_1);
x_159 = l_Lake_CacheService_downloadArtifact___closed__2;
x_160 = lean_string_append(x_158, x_159);
x_161 = lean_string_append(x_160, x_49);
x_162 = l_Lake_CacheService_downloadArtifact___closed__3;
x_163 = lean_string_append(x_161, x_162);
x_164 = lean_string_append(x_163, x_155);
x_165 = 1;
x_166 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set_uint8(x_166, sizeof(void*)*1, x_165);
lean_inc_ref(x_9);
x_167 = lean_apply_2(x_9, x_166, x_154);
x_168 = lean_ctor_get_uint8(x_3, sizeof(void*)*4);
lean_dec_ref(x_3);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec_ref(x_167);
x_170 = l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__2;
x_124 = x_155;
x_125 = x_169;
x_126 = x_170;
goto block_153;
}
else
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_167, 1);
lean_inc(x_171);
lean_dec_ref(x_167);
x_172 = l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__3;
x_124 = x_155;
x_125 = x_171;
x_126 = x_172;
goto block_153;
}
}
block_219:
{
uint8_t x_178; 
x_178 = lean_unbox(x_175);
lean_dec(x_175);
if (x_178 == 0)
{
x_154 = x_177;
goto block_173;
}
else
{
if (x_8 == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_179 = lean_unsigned_to_nat(0u);
x_180 = l_Lake_CacheMap_parse___closed__5;
x_181 = l_Lake_CacheMap_load(x_49, x_180, x_177);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec_ref(x_181);
x_184 = lean_ctor_get(x_182, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_182, 1);
lean_inc(x_185);
lean_dec_ref(x_182);
x_186 = lean_array_get_size(x_185);
x_187 = lean_nat_dec_lt(x_179, x_186);
if (x_187 == 0)
{
lean_dec(x_186);
lean_dec(x_185);
lean_dec_ref(x_9);
x_15 = x_184;
x_16 = x_183;
goto block_19;
}
else
{
uint8_t x_188; 
x_188 = lean_nat_dec_le(x_186, x_186);
if (x_188 == 0)
{
lean_dec(x_186);
lean_dec(x_185);
lean_dec_ref(x_9);
x_15 = x_184;
x_16 = x_183;
goto block_19;
}
else
{
lean_object* x_189; size_t x_190; size_t x_191; lean_object* x_192; lean_object* x_193; 
x_189 = lean_box(0);
x_190 = 0;
x_191 = lean_usize_of_nat(x_186);
lean_dec(x_186);
x_192 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0(x_185, x_190, x_191, x_189, x_9, x_183);
lean_dec(x_185);
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
lean_dec_ref(x_192);
x_15 = x_184;
x_16 = x_193;
goto block_19;
}
}
}
else
{
uint8_t x_194; 
x_194 = !lean_is_exclusive(x_181);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_195 = lean_ctor_get(x_181, 1);
x_196 = lean_ctor_get(x_181, 0);
lean_dec(x_196);
x_197 = lean_ctor_get(x_182, 1);
lean_inc(x_197);
lean_dec_ref(x_182);
x_198 = lean_array_get_size(x_197);
x_199 = lean_nat_dec_lt(x_179, x_198);
if (x_199 == 0)
{
lean_object* x_200; 
lean_dec(x_198);
lean_dec(x_197);
lean_dec_ref(x_9);
x_200 = lean_box(0);
lean_ctor_set_tag(x_181, 1);
lean_ctor_set(x_181, 0, x_200);
return x_181;
}
else
{
uint8_t x_201; 
lean_free_object(x_181);
x_201 = lean_nat_dec_le(x_198, x_198);
if (x_201 == 0)
{
lean_dec(x_198);
lean_dec(x_197);
lean_dec_ref(x_9);
x_11 = x_195;
goto block_14;
}
else
{
lean_object* x_202; size_t x_203; size_t x_204; lean_object* x_205; lean_object* x_206; 
x_202 = lean_box(0);
x_203 = 0;
x_204 = lean_usize_of_nat(x_198);
lean_dec(x_198);
x_205 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0(x_197, x_203, x_204, x_202, x_9, x_195);
lean_dec(x_197);
x_206 = lean_ctor_get(x_205, 1);
lean_inc(x_206);
lean_dec_ref(x_205);
x_11 = x_206;
goto block_14;
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_207 = lean_ctor_get(x_181, 1);
lean_inc(x_207);
lean_dec(x_181);
x_208 = lean_ctor_get(x_182, 1);
lean_inc(x_208);
lean_dec_ref(x_182);
x_209 = lean_array_get_size(x_208);
x_210 = lean_nat_dec_lt(x_179, x_209);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; 
lean_dec(x_209);
lean_dec(x_208);
lean_dec_ref(x_9);
x_211 = lean_box(0);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_207);
return x_212;
}
else
{
uint8_t x_213; 
x_213 = lean_nat_dec_le(x_209, x_209);
if (x_213 == 0)
{
lean_dec(x_209);
lean_dec(x_208);
lean_dec_ref(x_9);
x_11 = x_207;
goto block_14;
}
else
{
lean_object* x_214; size_t x_215; size_t x_216; lean_object* x_217; lean_object* x_218; 
x_214 = lean_box(0);
x_215 = 0;
x_216 = lean_usize_of_nat(x_209);
lean_dec(x_209);
x_217 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_CacheMap_parse_spec__0(x_208, x_215, x_216, x_214, x_9, x_207);
lean_dec(x_208);
x_218 = lean_ctor_get(x_217, 1);
lean_inc(x_218);
lean_dec_ref(x_217);
x_11 = x_218;
goto block_14;
}
}
}
}
}
else
{
x_154 = x_177;
goto block_173;
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
x_12 = l_Lake_CacheService_downloadRevisionOutputs_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11, x_9, x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
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
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadRevisionOutputs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
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
x_21 = lean_apply_2(x_7, x_20, x_8);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_23);
lean_dec_ref(x_3);
x_24 = l_Lake_CacheService_mapContentType___closed__0;
x_25 = l___private_Lake_Config_Cache_0__Lake_uploadS3___at___Lake_CacheService_uploadArtifact_spec__0(x_7, x_2, x_24, x_9, x_23, x_22);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadRevisionOutputs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_CacheService_uploadRevisionOutputs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
lean_object* initialize_Lake_Util_Log(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Artifact(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Trace(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_InstallPath(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Actions(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Url(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Proc(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Reservoir(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_IO(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Cache(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Log(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Artifact(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Trace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_InstallPath(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Actions(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Url(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Proc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Reservoir(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_IO(builtin, lean_io_mk_world());
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
l_Prod_fromJson_x3f___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__8___closed__0 = _init_l_Prod_fromJson_x3f___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__8___closed__0();
lean_mark_persistent(l_Prod_fromJson_x3f___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__8___closed__0);
l_Prod_fromJson_x3f___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__8___closed__1 = _init_l_Prod_fromJson_x3f___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__8___closed__1();
lean_mark_persistent(l_Prod_fromJson_x3f___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0_spec__8___closed__1);
l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__0 = _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__0();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__0);
l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__1 = _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__1();
lean_mark_persistent(l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at_____private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___closed__1);
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
l_Prod_toJson___at___Lake_CacheMap_updateFile_spec__0___closed__0 = _init_l_Prod_toJson___at___Lake_CacheMap_updateFile_spec__0___closed__0();
lean_mark_persistent(l_Prod_toJson___at___Lake_CacheMap_updateFile_spec__0___closed__0);
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

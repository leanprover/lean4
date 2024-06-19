// Lean compiler output
// Module: Lake.Build.Common
// Imports: Init Lake.Config.Monad Lake.Build.Actions
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
extern lean_object* l_Lake_MTime_instOrd;
LEAN_EXPORT lean_object* l_Lake_readTraceFile_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_compileO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31_(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileHash(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* lean_io_remove_file(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__1___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__6;
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_get_set_stdout(lean_object*, lean_object*);
static lean_object* l_Lake_computeDynlibOfShared___lambda__2___closed__1;
lean_object* l_Lake_compileSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_buildFileUnlessUpToDate___spec__2___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__1;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__2;
extern uint8_t l_System_Platform_isOSX;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_computeDynlibOfShared___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lake_computeArrayHash___at_Lake_buildO___spec__1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_computeTextFileHash(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_buildFileUnlessUpToDate___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildJob_collectList___rarg(lean_object*);
static lean_object* l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__2;
lean_object* lean_io_metadata(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_inputBinFile___closed__1;
static uint8_t l_Lake_buildUnlessUpToDate_x3f___rarg___lambda__1___closed__1;
static uint64_t l_Lake_platformTrace___closed__1;
lean_object* l_Lake_MTime_checkUpToDate___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
static uint64_t l_Lake_platformTrace___closed__2;
static lean_object* l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__9;
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at_Lake_inputTextFile___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_buildFileUnlessUpToDate___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_instOrdJobAction;
static lean_object* l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__4;
uint64_t lean_string_hash(lean_object*);
lean_object* l_List_bindTR_go___at___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1315____spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableRelLt___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__5;
lean_object* l_Lake_computeFileHash(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_instBEqHash;
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
static lean_object* l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__4;
LEAN_EXPORT lean_object* l_Lake_buildStaticLib(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_readTraceFile_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildTrace_mix(lean_object*, lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_buildFileUnlessUpToDate___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_compileExe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lake_buildFileUnlessUpToDate___spec__5___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_buildUnlessUpToDate_x3f___rarg___closed__3;
static lean_object* l_Lake_readTraceFile_x3f___closed__2;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__3;
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_sharedLibExt;
LEAN_EXPORT uint64_t l_Lake_platformTrace;
LEAN_EXPORT lean_object* l_Lake_inputBinFile(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_String_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepArray(lean_object*);
static lean_object* l_Lake_buildStaticLib___lambda__3___closed__1;
static lean_object* l_Lake_buildO___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_createParentDirs(lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_buildFileAfterDep___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
LEAN_EXPORT lean_object* l_Lake_computeDynlibOfShared___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__1;
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lake_buildStaticLib___spec__1(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFromJsonBuildMetadata;
lean_object* l_Lake_BuildJob_collectArray___rarg(lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepList___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__1___lambda__1(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_computeDynlibOfShared___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lake_instToJsonLog___spec__1(size_t, size_t, lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__7;
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__1___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__3;
uint8_t l_String_startsWith(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___at_Lake_buildFileUnlessUpToDate___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_panic___at_String_fromUTF8_x21___spec__1(lean_object*);
static lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__2___closed__2;
static lean_object* l_Lake_buildUnlessUpToDate_x3f___rarg___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_buildO___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__10;
LEAN_EXPORT lean_object* l_Lake_cacheFileHash(lean_object*, lean_object*);
lean_object* l_System_FilePath_fileStem(lean_object*);
static lean_object* l_Lake_cacheFileHash___closed__1;
extern lean_object* l_Task_Priority_default;
static lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__2___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_computeDynlibOfShared___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instMonadBaseIO;
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1(lean_object*, lean_object*);
static lean_object* l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__3;
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lake_buildFileUnlessUpToDate___spec__5(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_bignumFromJson_x3f(lean_object*);
extern lean_object* l_Lake_BuildTrace_nil;
static lean_object* l_Lake_buildLeanO___lambda__4___closed__1;
lean_object* lean_get_set_stderr(lean_object*, lean_object*);
static lean_object* l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__6;
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_computeDynlibOfShared___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lake_buildStaticLib___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__5;
lean_object* l_Array_mapMUnsafe_map___at_Lake_compileStaticLib___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79_(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_buildFileAfterDep___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildO___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lake_buildStaticLib___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_computeDynlibOfShared___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildUnlessUpToDate_x3f___rarg___closed__2;
static lean_object* l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__14;
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__2;
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_buildFileAfterDep___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__1___closed__3;
lean_object* l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeDynlibOfShared(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildLeanO___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate___spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepArray___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instToJsonBuildMetadata___closed__1;
LEAN_EXPORT lean_object* l_Lake_inputBinFile___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Hash_load_x3f(lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__15;
LEAN_EXPORT lean_object* l_Lake_inputTextFile___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instFromJsonBuildMetadata___closed__1;
static lean_object* l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__1;
LEAN_EXPORT lean_object* l_Lake_inputFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_readTraceFile_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at_Lake_inputBinFile___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepArray___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___at_Lake_buildO___spec__1___boxed(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern uint64_t l_Lake_Hash_nil;
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_buildFileUnlessUpToDate___spec__2___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__12;
LEAN_EXPORT lean_object* l_Lake_computeDynlibOfShared___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_computeDynlibOfShared___lambda__2___closed__3;
lean_object* l_Array_mapMUnsafe_map___at_Lake_instFromJsonLog___spec__1(size_t, size_t, lean_object*);
lean_object* lean_io_exit(uint8_t, lean_object*);
uint8_t l_instDecidableRelLe___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepList___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at_Lake_inputTextFile___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Array_foldlMUnsafe_fold___at_Lake_buildO___spec__2(lean_object*, size_t, size_t, uint64_t);
lean_object* lean_get_set_stdin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_computeDynlibOfShared___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___at_Lake_buildFileUnlessUpToDate___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___rarg___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_bignumToJson(lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lake_instToJsonBuildMetadata;
static lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_buildFileUnlessUpToDate___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__13;
LEAN_EXPORT lean_object* l_Lake_computeDynlibOfShared___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__11;
LEAN_EXPORT lean_object* l_Lake_buildO___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Array_foldlMUnsafe_fold___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_computeDynlibOfShared___lambda__2___closed__2;
lean_object* l_Lake_compileStaticLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeTraceFile(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildFileUnlessUpToDate___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern uint32_t l_Lake_noBuildCode;
LEAN_EXPORT lean_object* l_Lake_buildO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__1___closed__2;
static lean_object* l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__5;
static lean_object* l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__8;
lean_object* l_Lake_EStateT_instMonad___rarg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
static lean_object* l_Lake_readTraceFile_x3f___closed__1;
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
extern lean_object* l_System_Platform_target;
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f(lean_object*);
extern uint8_t l_System_Platform_isWindows;
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
lean_object* l_String_drop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildFileAfterDep___rarg___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lake_clearFileHash(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at_Lake_inputBinFile___spec__1(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__2;
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t _init_l_Lake_platformTrace___closed__1() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = l_System_Platform_target;
x_2 = lean_string_hash(x_1);
return x_2;
}
}
static uint64_t _init_l_Lake_platformTrace___closed__2() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = 1723;
x_2 = l_Lake_platformTrace___closed__1;
x_3 = lean_uint64_mix_hash(x_1, x_2);
return x_3;
}
}
static uint64_t _init_l_Lake_platformTrace() {
_start:
{
uint64_t x_1; 
x_1 = l_Lake_platformTrace___closed__2;
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("depHash", 7);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("log", 3);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint64_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_4 = lean_uint64_to_nat(x_3);
x_5 = l_Lean_bignumToJson(x_4);
x_6 = l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__1;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_array_get_size(x_10);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
x_14 = l_Array_mapMUnsafe_map___at_Lake_instToJsonLog___spec__1(x_12, x_13, x_10);
x_15 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__2;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_8);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_19);
x_21 = l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__3;
x_22 = l_List_bindTR_go___at___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1315____spec__1(x_20, x_21);
x_23 = l_Lean_Json_mkObj(x_22);
return x_23;
}
}
static lean_object* _init_l_Lake_instToJsonBuildMetadata___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instToJsonBuildMetadata() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instToJsonBuildMetadata___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__1___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_uint64_of_nat(x_1);
x_4 = lean_box_uint64(x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_cstr_to_nat("18446744073709551616");
return x_1;
}
}
static lean_object* _init_l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("value '{j}' is too large for `UInt64`", 37);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_bignumFromJson_x3f(x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__1___closed__1;
x_10 = lean_nat_dec_le(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_box(0);
x_12 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__1___lambda__1(x_8, x_11);
lean_dec(x_8);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
lean_object* x_16; 
lean_dec(x_8);
x_16 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__1___closed__3;
return x_16;
}
}
}
}
static lean_object* _init_l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("expected JSON array, got '", 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_unsigned_to_nat(80u);
x_5 = l_Lean_Json_pretty(x_3, x_4);
x_6 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__2___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__2___closed__2;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_unsigned_to_nat(80u);
x_12 = l_Lean_Json_pretty(x_3, x_11);
x_13 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__2___closed__1;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__2___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
case 4:
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
lean_dec(x_3);
x_19 = lean_array_get_size(x_18);
x_20 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_21 = 0;
x_22 = l_Array_mapMUnsafe_map___at_Lake_instFromJsonLog___spec__1(x_20, x_21, x_18);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_22, 0);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
default: 
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_unsigned_to_nat(80u);
lean_inc(x_3);
x_30 = l_Lean_Json_pretty(x_3, x_29);
x_31 = !lean_is_exclusive(x_3);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_3, 0);
lean_dec(x_32);
x_33 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__2___closed__1;
x_34 = lean_string_append(x_33, x_30);
lean_dec(x_30);
x_35 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__2___closed__2;
x_36 = lean_string_append(x_34, x_35);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_36);
return x_3;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_3);
x_37 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__2___closed__1;
x_38 = lean_string_append(x_37, x_30);
lean_dec(x_30);
x_39 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__2___closed__2;
x_40 = lean_string_append(x_38, x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lake", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("BuildMetadata", 13);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__1;
x_2 = l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__3;
x_2 = 1;
x_3 = l_Lean_Name_toString(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(".", 1);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__4;
x_2 = l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__8() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__7;
x_2 = 1;
x_3 = l_Lean_Name_toString(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__6;
x_2 = l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__8;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": ", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__9;
x_2 = l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__10;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__13() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__12;
x_2 = 1;
x_3 = l_Lean_Name_toString(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__6;
x_2 = l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__13;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__14;
x_2 = l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__10;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__1;
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__11;
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
x_9 = l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__11;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__2;
x_14 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__2(x_1, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__15;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__15;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_14, 0);
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__1___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instFromJsonBuildMetadata___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instFromJsonBuildMetadata() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instFromJsonBuildMetadata___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_readTraceFile_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lake_readTraceFile_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": read failed: ", 15);
return x_1;
}
}
static lean_object* _init_l_Lake_readTraceFile_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": invalid trace file: ", 22);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_readTraceFile_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_173; 
x_173 = l_IO_FS_readFile(x_1, x_3);
if (lean_obj_tag(x_173) == 0)
{
uint8_t x_174; 
x_174 = !lean_is_exclusive(x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_175 = lean_ctor_get(x_173, 0);
x_176 = lean_ctor_get(x_173, 1);
x_177 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_177, 0, x_175);
x_178 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_173, 1, x_2);
lean_ctor_set(x_173, 0, x_178);
x_4 = x_173;
x_5 = x_176;
goto block_172;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_179 = lean_ctor_get(x_173, 0);
x_180 = lean_ctor_get(x_173, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_173);
x_181 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_181, 0, x_179);
x_182 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_182, 0, x_181);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_2);
x_4 = x_183;
x_5 = x_180;
goto block_172;
}
}
else
{
uint8_t x_184; 
x_184 = !lean_is_exclusive(x_173);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_185 = lean_ctor_get(x_173, 0);
x_186 = lean_ctor_get(x_173, 1);
x_187 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_187, 0, x_185);
x_188 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set_tag(x_173, 0);
lean_ctor_set(x_173, 1, x_2);
lean_ctor_set(x_173, 0, x_188);
x_4 = x_173;
x_5 = x_186;
goto block_172;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_189 = lean_ctor_get(x_173, 0);
x_190 = lean_ctor_get(x_173, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_173);
x_191 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_191, 0, x_189);
x_192 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_192, 0, x_191);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_2);
x_4 = x_193;
x_5 = x_190;
goto block_172;
}
}
block_172:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_free_object(x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 11)
{
uint8_t x_10; 
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_4, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_4, 0, x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_dec(x_4);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_5);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_4);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_19 = lean_ctor_get(x_4, 1);
x_20 = lean_ctor_get(x_4, 0);
lean_dec(x_20);
x_21 = l_Lake_readTraceFile_x3f___closed__1;
x_22 = lean_string_append(x_21, x_1);
x_23 = l_Lake_readTraceFile_x3f___closed__2;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_io_error_to_string(x_9);
x_26 = lean_string_append(x_24, x_25);
lean_dec(x_25);
x_27 = lean_string_append(x_26, x_21);
x_28 = 2;
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
x_30 = lean_array_push(x_19, x_29);
x_31 = lean_box(0);
lean_ctor_set(x_4, 1, x_30);
lean_ctor_set(x_4, 0, x_31);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_5);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_33 = lean_ctor_get(x_4, 1);
lean_inc(x_33);
lean_dec(x_4);
x_34 = l_Lake_readTraceFile_x3f___closed__1;
x_35 = lean_string_append(x_34, x_1);
x_36 = l_Lake_readTraceFile_x3f___closed__2;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_io_error_to_string(x_9);
x_39 = lean_string_append(x_37, x_38);
lean_dec(x_38);
x_40 = lean_string_append(x_39, x_34);
x_41 = 2;
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
x_43 = lean_array_push(x_33, x_42);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_5);
return x_46;
}
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_4);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_4, 1);
x_49 = lean_ctor_get(x_4, 0);
lean_dec(x_49);
x_50 = lean_ctor_get(x_8, 0);
lean_inc(x_50);
lean_dec(x_8);
x_51 = l_Lean_Json_parse(x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_free_object(x_6);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec(x_51);
x_53 = l_Lake_readTraceFile_x3f___closed__1;
x_54 = lean_string_append(x_53, x_1);
x_55 = l_Lake_readTraceFile_x3f___closed__3;
x_56 = lean_string_append(x_54, x_55);
x_57 = lean_string_append(x_56, x_52);
lean_dec(x_52);
x_58 = lean_string_append(x_57, x_53);
x_59 = 0;
x_60 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_59);
x_61 = lean_array_push(x_48, x_60);
x_62 = lean_box(0);
lean_ctor_set(x_4, 1, x_61);
lean_ctor_set(x_4, 0, x_62);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_4);
lean_ctor_set(x_63, 1, x_5);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_51, 0);
lean_inc(x_64);
lean_dec(x_51);
x_65 = l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79_(x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_free_object(x_6);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec(x_65);
x_67 = l_Lake_readTraceFile_x3f___closed__1;
x_68 = lean_string_append(x_67, x_1);
x_69 = l_Lake_readTraceFile_x3f___closed__3;
x_70 = lean_string_append(x_68, x_69);
x_71 = lean_string_append(x_70, x_66);
lean_dec(x_66);
x_72 = lean_string_append(x_71, x_67);
x_73 = 0;
x_74 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set_uint8(x_74, sizeof(void*)*1, x_73);
x_75 = lean_array_push(x_48, x_74);
x_76 = lean_box(0);
lean_ctor_set(x_4, 1, x_75);
lean_ctor_set(x_4, 0, x_76);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_4);
lean_ctor_set(x_77, 1, x_5);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_65, 0);
lean_inc(x_78);
lean_dec(x_65);
lean_ctor_set(x_6, 0, x_78);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_5);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_4, 1);
lean_inc(x_80);
lean_dec(x_4);
x_81 = lean_ctor_get(x_8, 0);
lean_inc(x_81);
lean_dec(x_8);
x_82 = l_Lean_Json_parse(x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_free_object(x_6);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec(x_82);
x_84 = l_Lake_readTraceFile_x3f___closed__1;
x_85 = lean_string_append(x_84, x_1);
x_86 = l_Lake_readTraceFile_x3f___closed__3;
x_87 = lean_string_append(x_85, x_86);
x_88 = lean_string_append(x_87, x_83);
lean_dec(x_83);
x_89 = lean_string_append(x_88, x_84);
x_90 = 0;
x_91 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set_uint8(x_91, sizeof(void*)*1, x_90);
x_92 = lean_array_push(x_80, x_91);
x_93 = lean_box(0);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_5);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_82, 0);
lean_inc(x_96);
lean_dec(x_82);
x_97 = l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79_(x_96);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_free_object(x_6);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec(x_97);
x_99 = l_Lake_readTraceFile_x3f___closed__1;
x_100 = lean_string_append(x_99, x_1);
x_101 = l_Lake_readTraceFile_x3f___closed__3;
x_102 = lean_string_append(x_100, x_101);
x_103 = lean_string_append(x_102, x_98);
lean_dec(x_98);
x_104 = lean_string_append(x_103, x_99);
x_105 = 0;
x_106 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set_uint8(x_106, sizeof(void*)*1, x_105);
x_107 = lean_array_push(x_80, x_106);
x_108 = lean_box(0);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_5);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_97, 0);
lean_inc(x_111);
lean_dec(x_97);
lean_ctor_set(x_6, 0, x_111);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_6);
lean_ctor_set(x_112, 1, x_80);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_5);
return x_113;
}
}
}
}
}
else
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_6, 0);
lean_inc(x_114);
lean_dec(x_6);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
lean_dec(x_114);
if (lean_obj_tag(x_115) == 11)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_115);
x_116 = lean_ctor_get(x_4, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_117 = x_4;
} else {
 lean_dec_ref(x_4);
 x_117 = lean_box(0);
}
x_118 = lean_box(0);
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_116);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_5);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_121 = lean_ctor_get(x_4, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_122 = x_4;
} else {
 lean_dec_ref(x_4);
 x_122 = lean_box(0);
}
x_123 = l_Lake_readTraceFile_x3f___closed__1;
x_124 = lean_string_append(x_123, x_1);
x_125 = l_Lake_readTraceFile_x3f___closed__2;
x_126 = lean_string_append(x_124, x_125);
x_127 = lean_io_error_to_string(x_115);
x_128 = lean_string_append(x_126, x_127);
lean_dec(x_127);
x_129 = lean_string_append(x_128, x_123);
x_130 = 2;
x_131 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set_uint8(x_131, sizeof(void*)*1, x_130);
x_132 = lean_array_push(x_121, x_131);
x_133 = lean_box(0);
if (lean_is_scalar(x_122)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_122;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_132);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_5);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_136 = lean_ctor_get(x_4, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_137 = x_4;
} else {
 lean_dec_ref(x_4);
 x_137 = lean_box(0);
}
x_138 = lean_ctor_get(x_114, 0);
lean_inc(x_138);
lean_dec(x_114);
x_139 = l_Lean_Json_parse(x_138);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_dec(x_139);
x_141 = l_Lake_readTraceFile_x3f___closed__1;
x_142 = lean_string_append(x_141, x_1);
x_143 = l_Lake_readTraceFile_x3f___closed__3;
x_144 = lean_string_append(x_142, x_143);
x_145 = lean_string_append(x_144, x_140);
lean_dec(x_140);
x_146 = lean_string_append(x_145, x_141);
x_147 = 0;
x_148 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set_uint8(x_148, sizeof(void*)*1, x_147);
x_149 = lean_array_push(x_136, x_148);
x_150 = lean_box(0);
if (lean_is_scalar(x_137)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_137;
}
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_149);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_5);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_139, 0);
lean_inc(x_153);
lean_dec(x_139);
x_154 = l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79_(x_153);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
lean_dec(x_154);
x_156 = l_Lake_readTraceFile_x3f___closed__1;
x_157 = lean_string_append(x_156, x_1);
x_158 = l_Lake_readTraceFile_x3f___closed__3;
x_159 = lean_string_append(x_157, x_158);
x_160 = lean_string_append(x_159, x_155);
lean_dec(x_155);
x_161 = lean_string_append(x_160, x_156);
x_162 = 0;
x_163 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set_uint8(x_163, sizeof(void*)*1, x_162);
x_164 = lean_array_push(x_136, x_163);
x_165 = lean_box(0);
if (lean_is_scalar(x_137)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_137;
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_164);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_5);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_168 = lean_ctor_get(x_154, 0);
lean_inc(x_168);
lean_dec(x_154);
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_168);
if (lean_is_scalar(x_137)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_137;
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_136);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_5);
return x_171;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_readTraceFile_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_readTraceFile_x3f(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_writeTraceFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = l_Lake_createParentDirs(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 1);
lean_dec(x_8);
lean_ctor_set(x_2, 1, x_3);
x_9 = l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31_(x_2);
x_10 = lean_unsigned_to_nat(80u);
x_11 = l_Lean_Json_pretty(x_9, x_10);
x_12 = l_IO_FS_writeFile(x_1, x_11, x_6);
lean_dec(x_11);
lean_dec(x_1);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
x_15 = l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31_(x_14);
x_16 = lean_unsigned_to_nat(80u);
x_17 = l_Lean_Json_pretty(x_15, x_16);
x_18 = l_IO_FS_writeFile(x_1, x_17, x_6);
lean_dec(x_17);
lean_dec(x_1);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
return x_5;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_5, 0);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_5);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
lean_dec(x_12);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = l_Lake_instBEqHash;
x_15 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____rarg(x_14, x_13, x_5);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_1);
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
if (x_18 == 0)
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_19 = 0;
x_20 = lean_box(x_19);
lean_ctor_set(x_4, 1, x_8);
lean_ctor_set(x_4, 0, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_9);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_8);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lake_MTime_checkUpToDate___rarg(x_2, x_3, x_6, x_9);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_ctor_set(x_4, 1, x_8);
lean_ctor_set(x_4, 0, x_25);
lean_ctor_set(x_23, 0, x_4);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_23);
lean_ctor_set(x_4, 1, x_8);
lean_ctor_set(x_4, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_4);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_8, 0);
x_30 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
lean_inc(x_29);
lean_dec(x_8);
x_31 = l_Lake_MTime_checkUpToDate___rarg(x_2, x_3, x_6, x_9);
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
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_30);
lean_ctor_set(x_4, 1, x_35);
lean_ctor_set(x_4, 0, x_32);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_4);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_6);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_8);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_8, 0);
x_39 = lean_apply_2(x_1, x_3, x_9);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_ctor_set(x_4, 1, x_8);
lean_ctor_set(x_4, 0, x_41);
lean_ctor_set(x_39, 0, x_4);
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
lean_ctor_set(x_4, 1, x_8);
lean_ctor_set(x_4, 0, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_4);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_free_object(x_8);
lean_dec(x_38);
lean_free_object(x_4);
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
return x_39;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_39, 0);
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_39);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; uint8_t x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_8, 0);
x_50 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
lean_inc(x_49);
lean_dec(x_8);
x_51 = lean_apply_2(x_1, x_3, x_9);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_54 = x_51;
} else {
 lean_dec_ref(x_51);
 x_54 = lean_box(0);
}
x_55 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_50);
lean_ctor_set(x_4, 1, x_55);
lean_ctor_set(x_4, 0, x_52);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_4);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_49);
lean_free_object(x_4);
x_57 = lean_ctor_get(x_51, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_51, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_59 = x_51;
} else {
 lean_dec_ref(x_51);
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
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_61 = lean_ctor_get(x_4, 0);
lean_inc(x_61);
lean_dec(x_4);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = l_Lake_instBEqHash;
x_64 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____rarg(x_63, x_62, x_5);
x_65 = lean_unbox(x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
lean_dec(x_1);
x_66 = lean_ctor_get(x_7, 0);
x_67 = lean_ctor_get_uint8(x_66, sizeof(void*)*1);
if (x_67 == 0)
{
uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_68 = 0;
x_69 = lean_box(x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_8);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_9);
return x_71;
}
else
{
lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_72 = lean_ctor_get(x_8, 0);
lean_inc(x_72);
x_73 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_74 = x_8;
} else {
 lean_dec_ref(x_8);
 x_74 = lean_box(0);
}
x_75 = l_Lake_MTime_checkUpToDate___rarg(x_2, x_3, x_6, x_9);
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
if (lean_is_scalar(x_74)) {
 x_79 = lean_alloc_ctor(0, 1, 1);
} else {
 x_79 = x_74;
}
lean_ctor_set(x_79, 0, x_72);
lean_ctor_set_uint8(x_79, sizeof(void*)*1, x_73);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_80, 1, x_79);
if (lean_is_scalar(x_78)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_78;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_77);
return x_81;
}
}
else
{
lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_6);
lean_dec(x_2);
x_82 = lean_ctor_get(x_8, 0);
lean_inc(x_82);
x_83 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_84 = x_8;
} else {
 lean_dec_ref(x_8);
 x_84 = lean_box(0);
}
x_85 = lean_apply_2(x_1, x_3, x_9);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
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
if (lean_is_scalar(x_84)) {
 x_89 = lean_alloc_ctor(0, 1, 1);
} else {
 x_89 = x_84;
}
lean_ctor_set(x_89, 0, x_82);
lean_ctor_set_uint8(x_89, sizeof(void*)*1, x_83);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_86);
lean_ctor_set(x_90, 1, x_89);
if (lean_is_scalar(x_88)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_88;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_87);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_84);
lean_dec(x_82);
x_92 = lean_ctor_get(x_85, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_85, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_94 = x_85;
} else {
 lean_dec_ref(x_85);
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
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_checkHashUpToDate___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_checkHashUpToDate___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_10;
}
}
static uint8_t _init_l_Lake_buildUnlessUpToDate_x3f___rarg___lambda__1___closed__1() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = l_Lake_noBuildCode;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_108; uint8_t x_109; 
x_108 = lean_ctor_get(x_6, 0);
lean_inc(x_108);
x_109 = lean_ctor_get_uint8(x_108, sizeof(void*)*1 + 2);
lean_dec(x_108);
if (x_109 == 0)
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_7);
if (x_110 == 0)
{
uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_111 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
x_112 = l_Lake_instOrdJobAction;
x_113 = lean_box(x_111);
x_114 = lean_box(x_4);
x_115 = l_instDecidableRelLe___rarg(x_112, x_113, x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_box(0);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_7);
x_9 = x_117;
x_10 = x_8;
goto block_107;
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_4);
x_118 = lean_box(0);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_7);
x_9 = x_119;
x_10 = x_8;
goto block_107;
}
}
else
{
lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_120 = lean_ctor_get(x_7, 0);
x_121 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
lean_inc(x_120);
lean_dec(x_7);
x_122 = l_Lake_instOrdJobAction;
x_123 = lean_box(x_121);
x_124 = lean_box(x_4);
x_125 = l_instDecidableRelLe___rarg(x_122, x_123, x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_126, 0, x_120);
lean_ctor_set_uint8(x_126, sizeof(void*)*1, x_121);
x_127 = lean_box(0);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_126);
x_9 = x_128;
x_10 = x_8;
goto block_107;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_129, 0, x_120);
lean_ctor_set_uint8(x_129, sizeof(void*)*1, x_4);
x_130 = lean_box(0);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
x_9 = x_131;
x_10 = x_8;
goto block_107;
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_132 = !lean_is_exclusive(x_7);
if (x_132 == 0)
{
lean_object* x_133; uint8_t x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_7, 0);
x_134 = l_Lake_buildUnlessUpToDate_x3f___rarg___lambda__1___closed__1;
x_135 = lean_io_exit(x_134, x_8);
if (lean_obj_tag(x_135) == 0)
{
uint8_t x_136; 
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_135, 0);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_7);
lean_ctor_set(x_135, 0, x_138);
return x_135;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_139 = lean_ctor_get(x_135, 0);
x_140 = lean_ctor_get(x_135, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_135);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_7);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
else
{
uint8_t x_143; 
x_143 = !lean_is_exclusive(x_135);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_144 = lean_ctor_get(x_135, 0);
x_145 = lean_io_error_to_string(x_144);
x_146 = 3;
x_147 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set_uint8(x_147, sizeof(void*)*1, x_146);
x_148 = lean_array_get_size(x_133);
x_149 = lean_array_push(x_133, x_147);
lean_ctor_set(x_7, 0, x_149);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_7);
lean_ctor_set_tag(x_135, 0);
lean_ctor_set(x_135, 0, x_150);
return x_135;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_151 = lean_ctor_get(x_135, 0);
x_152 = lean_ctor_get(x_135, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_135);
x_153 = lean_io_error_to_string(x_151);
x_154 = 3;
x_155 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set_uint8(x_155, sizeof(void*)*1, x_154);
x_156 = lean_array_get_size(x_133);
x_157 = lean_array_push(x_133, x_155);
lean_ctor_set(x_7, 0, x_157);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_7);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_152);
return x_159;
}
}
}
else
{
lean_object* x_160; uint8_t x_161; uint8_t x_162; lean_object* x_163; 
x_160 = lean_ctor_get(x_7, 0);
x_161 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
lean_inc(x_160);
lean_dec(x_7);
x_162 = l_Lake_buildUnlessUpToDate_x3f___rarg___lambda__1___closed__1;
x_163 = lean_io_exit(x_162, x_8);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
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
x_167 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_167, 0, x_160);
lean_ctor_set_uint8(x_167, sizeof(void*)*1, x_161);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_164);
lean_ctor_set(x_168, 1, x_167);
if (lean_is_scalar(x_166)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_166;
}
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_165);
return x_169;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_170 = lean_ctor_get(x_163, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_163, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_172 = x_163;
} else {
 lean_dec_ref(x_163);
 x_172 = lean_box(0);
}
x_173 = lean_io_error_to_string(x_170);
x_174 = 3;
x_175 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set_uint8(x_175, sizeof(void*)*1, x_174);
x_176 = lean_array_get_size(x_160);
x_177 = lean_array_push(x_160, x_175);
x_178 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set_uint8(x_178, sizeof(void*)*1, x_161);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_178);
if (lean_is_scalar(x_172)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_172;
 lean_ctor_set_tag(x_180, 0);
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_171);
return x_180;
}
}
}
block_107:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_array_get_size(x_12);
lean_dec(x_12);
x_14 = lean_apply_3(x_1, x_6, x_11, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_15, 1);
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_array_get_size(x_21);
x_23 = l_Array_extract___rarg(x_21, x_13, x_22);
x_24 = l_Lake_writeTraceFile(x_2, x_3, x_23, x_19);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_22);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = 0;
x_28 = lean_box(x_27);
lean_ctor_set(x_15, 0, x_28);
lean_ctor_set(x_24, 0, x_15);
return x_24;
}
else
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = 0;
x_31 = lean_box(x_30);
lean_ctor_set(x_15, 0, x_31);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_15);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_24);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_24, 0);
x_35 = lean_io_error_to_string(x_34);
x_36 = 3;
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_36);
x_38 = lean_array_push(x_21, x_37);
lean_ctor_set(x_17, 0, x_38);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_22);
lean_ctor_set_tag(x_24, 0);
lean_ctor_set(x_24, 0, x_15);
return x_24;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_24, 0);
x_40 = lean_ctor_get(x_24, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_24);
x_41 = lean_io_error_to_string(x_39);
x_42 = 3;
x_43 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_42);
x_44 = lean_array_push(x_21, x_43);
lean_ctor_set(x_17, 0, x_44);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_22);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_15);
lean_ctor_set(x_45, 1, x_40);
return x_45;
}
}
}
else
{
lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_17, 0);
x_47 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
lean_inc(x_46);
lean_dec(x_17);
x_48 = lean_array_get_size(x_46);
x_49 = l_Array_extract___rarg(x_46, x_13, x_48);
x_50 = l_Lake_writeTraceFile(x_2, x_3, x_49, x_19);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_48);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_52 = x_50;
} else {
 lean_dec_ref(x_50);
 x_52 = lean_box(0);
}
x_53 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_53, 0, x_46);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_47);
x_54 = 0;
x_55 = lean_box(x_54);
lean_ctor_set(x_15, 1, x_53);
lean_ctor_set(x_15, 0, x_55);
if (lean_is_scalar(x_52)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_52;
}
lean_ctor_set(x_56, 0, x_15);
lean_ctor_set(x_56, 1, x_51);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_57 = lean_ctor_get(x_50, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_50, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_59 = x_50;
} else {
 lean_dec_ref(x_50);
 x_59 = lean_box(0);
}
x_60 = lean_io_error_to_string(x_57);
x_61 = 3;
x_62 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_61);
x_63 = lean_array_push(x_46, x_62);
x_64 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_47);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 1, x_64);
lean_ctor_set(x_15, 0, x_48);
if (lean_is_scalar(x_59)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_59;
 lean_ctor_set_tag(x_65, 0);
}
lean_ctor_set(x_65, 0, x_15);
lean_ctor_set(x_65, 1, x_58);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_66 = lean_ctor_get(x_15, 1);
lean_inc(x_66);
lean_dec(x_15);
x_67 = lean_ctor_get(x_14, 1);
lean_inc(x_67);
lean_dec(x_14);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_66, sizeof(void*)*1);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_70 = x_66;
} else {
 lean_dec_ref(x_66);
 x_70 = lean_box(0);
}
x_71 = lean_array_get_size(x_68);
x_72 = l_Array_extract___rarg(x_68, x_13, x_71);
x_73 = l_Lake_writeTraceFile(x_2, x_3, x_72, x_67);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_71);
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
if (lean_is_scalar(x_70)) {
 x_76 = lean_alloc_ctor(0, 1, 1);
} else {
 x_76 = x_70;
}
lean_ctor_set(x_76, 0, x_68);
lean_ctor_set_uint8(x_76, sizeof(void*)*1, x_69);
x_77 = 0;
x_78 = lean_box(x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_76);
if (lean_is_scalar(x_75)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_75;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_74);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_81 = lean_ctor_get(x_73, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_73, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_83 = x_73;
} else {
 lean_dec_ref(x_73);
 x_83 = lean_box(0);
}
x_84 = lean_io_error_to_string(x_81);
x_85 = 3;
x_86 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set_uint8(x_86, sizeof(void*)*1, x_85);
x_87 = lean_array_push(x_68, x_86);
if (lean_is_scalar(x_70)) {
 x_88 = lean_alloc_ctor(0, 1, 1);
} else {
 x_88 = x_70;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set_uint8(x_88, sizeof(void*)*1, x_69);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_71);
lean_ctor_set(x_89, 1, x_88);
if (lean_is_scalar(x_83)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_83;
 lean_ctor_set_tag(x_90, 0);
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_82);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
x_91 = !lean_is_exclusive(x_14);
if (x_91 == 0)
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_ctor_get(x_14, 0);
lean_dec(x_92);
x_93 = !lean_is_exclusive(x_15);
if (x_93 == 0)
{
return x_14;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_15, 0);
x_95 = lean_ctor_get(x_15, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_15);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set(x_14, 0, x_96);
return x_14;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_97 = lean_ctor_get(x_14, 1);
lean_inc(x_97);
lean_dec(x_14);
x_98 = lean_ctor_get(x_15, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_15, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_100 = x_15;
} else {
 lean_dec_ref(x_15);
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
else
{
uint8_t x_103; 
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
x_103 = !lean_is_exclusive(x_14);
if (x_103 == 0)
{
return x_14;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_14, 0);
x_105 = lean_ctor_get(x_14, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_14);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_array_push(x_7, x_2);
lean_ctor_set(x_4, 0, x_8);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_inc(x_12);
lean_dec(x_4);
x_14 = lean_array_push(x_12, x_2);
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_13);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
return x_18;
}
}
}
static lean_object* _init_l_Lake_buildUnlessUpToDate_x3f___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instMonadBaseIO;
x_2 = l_Lake_EStateT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_buildUnlessUpToDate_x3f___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_buildUnlessUpToDate_x3f___rarg___closed__1;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_buildUnlessUpToDate_x3f___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_buildUnlessUpToDate_x3f___rarg___lambda__2___boxed), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_416; 
x_416 = !lean_is_exclusive(x_10);
if (x_416 == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; 
x_417 = lean_ctor_get(x_10, 0);
x_418 = l_Lake_readTraceFile_x3f(x_5, x_417, x_11);
x_419 = lean_ctor_get(x_418, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_418, 1);
lean_inc(x_420);
lean_dec(x_418);
x_421 = !lean_is_exclusive(x_419);
if (x_421 == 0)
{
lean_object* x_422; 
x_422 = lean_ctor_get(x_419, 1);
lean_ctor_set(x_10, 0, x_422);
lean_ctor_set(x_419, 1, x_10);
x_12 = x_419;
x_13 = x_420;
goto block_415;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_423 = lean_ctor_get(x_419, 0);
x_424 = lean_ctor_get(x_419, 1);
lean_inc(x_424);
lean_inc(x_423);
lean_dec(x_419);
lean_ctor_set(x_10, 0, x_424);
x_425 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_425, 0, x_423);
lean_ctor_set(x_425, 1, x_10);
x_12 = x_425;
x_13 = x_420;
goto block_415;
}
}
else
{
lean_object* x_426; uint8_t x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_426 = lean_ctor_get(x_10, 0);
x_427 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
lean_inc(x_426);
lean_dec(x_10);
x_428 = l_Lake_readTraceFile_x3f(x_5, x_426, x_11);
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_428, 1);
lean_inc(x_430);
lean_dec(x_428);
x_431 = lean_ctor_get(x_429, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_429, 1);
lean_inc(x_432);
if (lean_is_exclusive(x_429)) {
 lean_ctor_release(x_429, 0);
 lean_ctor_release(x_429, 1);
 x_433 = x_429;
} else {
 lean_dec_ref(x_429);
 x_433 = lean_box(0);
}
x_434 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_434, 0, x_432);
lean_ctor_set_uint8(x_434, sizeof(void*)*1, x_427);
if (lean_is_scalar(x_433)) {
 x_435 = lean_alloc_ctor(0, 2, 0);
} else {
 x_435 = x_433;
}
lean_ctor_set(x_435, 0, x_431);
lean_ctor_set(x_435, 1, x_434);
x_12 = x_435;
x_13 = x_430;
goto block_415;
}
block_415:
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_8);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_12, 1);
x_19 = lean_ctor_get(x_12, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
x_22 = l_Lake_MTime_checkUpToDate___rarg(x_2, x_3, x_21, x_13);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = lean_unbox(x_24);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_free_object(x_22);
lean_free_object(x_12);
x_27 = lean_box(0);
x_28 = l_Lake_buildUnlessUpToDate_x3f___rarg___lambda__1(x_6, x_5, x_4, x_7, x_27, x_9, x_18, x_25);
return x_28;
}
else
{
uint8_t x_29; lean_object* x_30; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_29 = 1;
x_30 = lean_box(x_29);
lean_ctor_set(x_12, 0, x_30);
lean_ctor_set(x_22, 0, x_12);
return x_22;
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_22, 0);
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_22);
x_33 = lean_unbox(x_31);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_free_object(x_12);
x_34 = lean_box(0);
x_35 = l_Lake_buildUnlessUpToDate_x3f___rarg___lambda__1(x_6, x_5, x_4, x_7, x_34, x_9, x_18, x_32);
return x_35;
}
else
{
uint8_t x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_36 = 1;
x_37 = lean_box(x_36);
lean_ctor_set(x_12, 0, x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_12);
lean_ctor_set(x_38, 1, x_32);
return x_38;
}
}
}
else
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_39 = lean_ctor_get(x_18, 0);
x_40 = lean_ctor_get_uint8(x_18, sizeof(void*)*1);
lean_inc(x_39);
lean_dec(x_18);
x_41 = lean_ctor_get(x_4, 1);
lean_inc(x_41);
x_42 = l_Lake_MTime_checkUpToDate___rarg(x_2, x_3, x_41, x_13);
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
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_40);
x_47 = lean_unbox(x_43);
lean_dec(x_43);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_45);
lean_free_object(x_12);
x_48 = lean_box(0);
x_49 = l_Lake_buildUnlessUpToDate_x3f___rarg___lambda__1(x_6, x_5, x_4, x_7, x_48, x_9, x_46, x_44);
return x_49;
}
else
{
uint8_t x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_50 = 1;
x_51 = lean_box(x_50);
lean_ctor_set(x_12, 1, x_46);
lean_ctor_set(x_12, 0, x_51);
if (lean_is_scalar(x_45)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_45;
}
lean_ctor_set(x_52, 0, x_12);
lean_ctor_set(x_52, 1, x_44);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_53 = lean_ctor_get(x_12, 1);
lean_inc(x_53);
lean_dec(x_12);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get_uint8(x_53, sizeof(void*)*1);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_56 = x_53;
} else {
 lean_dec_ref(x_53);
 x_56 = lean_box(0);
}
x_57 = lean_ctor_get(x_4, 1);
lean_inc(x_57);
x_58 = l_Lake_MTime_checkUpToDate___rarg(x_2, x_3, x_57, x_13);
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
if (lean_is_scalar(x_56)) {
 x_62 = lean_alloc_ctor(0, 1, 1);
} else {
 x_62 = x_56;
}
lean_ctor_set(x_62, 0, x_54);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_55);
x_63 = lean_unbox(x_59);
lean_dec(x_59);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_61);
x_64 = lean_box(0);
x_65 = l_Lake_buildUnlessUpToDate_x3f___rarg___lambda__1(x_6, x_5, x_4, x_7, x_64, x_9, x_62, x_60);
return x_65;
}
else
{
uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_66 = 1;
x_67 = lean_box(x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_62);
if (lean_is_scalar(x_61)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_61;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_60);
return x_69;
}
}
}
else
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_12);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_ctor_get(x_12, 1);
x_72 = lean_ctor_get(x_12, 0);
lean_dec(x_72);
x_73 = !lean_is_exclusive(x_71);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = l_Lake_MTime_checkUpToDate___rarg(x_2, x_3, x_8, x_13);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = lean_ctor_get(x_74, 0);
x_77 = lean_ctor_get(x_74, 1);
x_78 = lean_unbox(x_76);
lean_dec(x_76);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_free_object(x_74);
lean_free_object(x_12);
x_79 = lean_box(0);
x_80 = l_Lake_buildUnlessUpToDate_x3f___rarg___lambda__1(x_6, x_5, x_4, x_7, x_79, x_9, x_71, x_77);
return x_80;
}
else
{
uint8_t x_81; lean_object* x_82; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_81 = 1;
x_82 = lean_box(x_81);
lean_ctor_set(x_12, 0, x_82);
lean_ctor_set(x_74, 0, x_12);
return x_74;
}
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = lean_ctor_get(x_74, 0);
x_84 = lean_ctor_get(x_74, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_74);
x_85 = lean_unbox(x_83);
lean_dec(x_83);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_free_object(x_12);
x_86 = lean_box(0);
x_87 = l_Lake_buildUnlessUpToDate_x3f___rarg___lambda__1(x_6, x_5, x_4, x_7, x_86, x_9, x_71, x_84);
return x_87;
}
else
{
uint8_t x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_88 = 1;
x_89 = lean_box(x_88);
lean_ctor_set(x_12, 0, x_89);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_12);
lean_ctor_set(x_90, 1, x_84);
return x_90;
}
}
}
else
{
lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_91 = lean_ctor_get(x_71, 0);
x_92 = lean_ctor_get_uint8(x_71, sizeof(void*)*1);
lean_inc(x_91);
lean_dec(x_71);
x_93 = l_Lake_MTime_checkUpToDate___rarg(x_2, x_3, x_8, x_13);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_96 = x_93;
} else {
 lean_dec_ref(x_93);
 x_96 = lean_box(0);
}
x_97 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_97, 0, x_91);
lean_ctor_set_uint8(x_97, sizeof(void*)*1, x_92);
x_98 = lean_unbox(x_94);
lean_dec(x_94);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_96);
lean_free_object(x_12);
x_99 = lean_box(0);
x_100 = l_Lake_buildUnlessUpToDate_x3f___rarg___lambda__1(x_6, x_5, x_4, x_7, x_99, x_9, x_97, x_95);
return x_100;
}
else
{
uint8_t x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_101 = 1;
x_102 = lean_box(x_101);
lean_ctor_set(x_12, 1, x_97);
lean_ctor_set(x_12, 0, x_102);
if (lean_is_scalar(x_96)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_96;
}
lean_ctor_set(x_103, 0, x_12);
lean_ctor_set(x_103, 1, x_95);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_104 = lean_ctor_get(x_12, 1);
lean_inc(x_104);
lean_dec(x_12);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get_uint8(x_104, sizeof(void*)*1);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 x_107 = x_104;
} else {
 lean_dec_ref(x_104);
 x_107 = lean_box(0);
}
x_108 = l_Lake_MTime_checkUpToDate___rarg(x_2, x_3, x_8, x_13);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_111 = x_108;
} else {
 lean_dec_ref(x_108);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_112 = lean_alloc_ctor(0, 1, 1);
} else {
 x_112 = x_107;
}
lean_ctor_set(x_112, 0, x_105);
lean_ctor_set_uint8(x_112, sizeof(void*)*1, x_106);
x_113 = lean_unbox(x_109);
lean_dec(x_109);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_111);
x_114 = lean_box(0);
x_115 = l_Lake_buildUnlessUpToDate_x3f___rarg___lambda__1(x_6, x_5, x_4, x_7, x_114, x_9, x_112, x_110);
return x_115;
}
else
{
uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_116 = 1;
x_117 = lean_box(x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_112);
if (lean_is_scalar(x_111)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_111;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_110);
return x_119;
}
}
}
}
else
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_14);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = lean_ctor_get(x_14, 0);
x_122 = lean_ctor_get(x_12, 1);
lean_inc(x_122);
lean_dec(x_12);
x_123 = lean_ctor_get(x_121, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
lean_dec(x_121);
lean_ctor_set(x_14, 0, x_123);
lean_inc(x_4);
x_125 = l_Lake_checkHashUpToDate___rarg(x_1, x_2, x_3, x_4, x_14, x_8, x_9, x_122, x_13);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_128 = x_125;
} else {
 lean_dec_ref(x_125);
 x_128 = lean_box(0);
}
x_129 = !lean_is_exclusive(x_126);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_229; 
x_130 = lean_ctor_get(x_126, 0);
x_131 = lean_ctor_get(x_126, 1);
x_229 = lean_unbox(x_130);
lean_dec(x_130);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; 
lean_free_object(x_126);
lean_dec(x_128);
lean_dec(x_124);
x_230 = lean_box(0);
x_231 = l_Lake_buildUnlessUpToDate_x3f___rarg___lambda__1(x_6, x_5, x_4, x_7, x_230, x_9, x_131, x_127);
return x_231;
}
else
{
uint8_t x_232; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_232 = !lean_is_exclusive(x_131);
if (x_232 == 0)
{
uint8_t x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; 
x_233 = lean_ctor_get_uint8(x_131, sizeof(void*)*1);
x_234 = l_Lake_instOrdJobAction;
x_235 = 1;
x_236 = lean_box(x_233);
x_237 = lean_box(x_235);
x_238 = l_instDecidableRelLe___rarg(x_234, x_236, x_237);
if (x_238 == 0)
{
lean_object* x_239; 
x_239 = lean_box(0);
lean_ctor_set(x_126, 0, x_239);
x_132 = x_126;
x_133 = x_127;
goto block_228;
}
else
{
lean_object* x_240; 
lean_ctor_set_uint8(x_131, sizeof(void*)*1, x_235);
x_240 = lean_box(0);
lean_ctor_set(x_126, 0, x_240);
x_132 = x_126;
x_133 = x_127;
goto block_228;
}
}
else
{
lean_object* x_241; uint8_t x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
x_241 = lean_ctor_get(x_131, 0);
x_242 = lean_ctor_get_uint8(x_131, sizeof(void*)*1);
lean_inc(x_241);
lean_dec(x_131);
x_243 = l_Lake_instOrdJobAction;
x_244 = 1;
x_245 = lean_box(x_242);
x_246 = lean_box(x_244);
x_247 = l_instDecidableRelLe___rarg(x_243, x_245, x_246);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; 
x_248 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_248, 0, x_241);
lean_ctor_set_uint8(x_248, sizeof(void*)*1, x_242);
x_249 = lean_box(0);
lean_ctor_set(x_126, 1, x_248);
lean_ctor_set(x_126, 0, x_249);
x_132 = x_126;
x_133 = x_127;
goto block_228;
}
else
{
lean_object* x_250; lean_object* x_251; 
x_250 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_250, 0, x_241);
lean_ctor_set_uint8(x_250, sizeof(void*)*1, x_244);
x_251 = lean_box(0);
lean_ctor_set(x_126, 1, x_250);
lean_ctor_set(x_126, 0, x_251);
x_132 = x_126;
x_133 = x_127;
goto block_228;
}
}
}
block_228:
{
uint8_t x_134; 
x_134 = !lean_is_exclusive(x_132);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_135 = lean_ctor_get(x_132, 1);
x_136 = lean_ctor_get(x_132, 0);
lean_dec(x_136);
x_137 = lean_array_get_size(x_124);
x_138 = lean_unsigned_to_nat(0u);
x_139 = lean_nat_dec_lt(x_138, x_137);
if (x_139 == 0)
{
uint8_t x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_137);
lean_dec(x_124);
lean_dec(x_9);
x_140 = 1;
x_141 = lean_box(x_140);
lean_ctor_set(x_132, 0, x_141);
if (lean_is_scalar(x_128)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_128;
}
lean_ctor_set(x_142, 0, x_132);
lean_ctor_set(x_142, 1, x_133);
return x_142;
}
else
{
uint8_t x_143; 
x_143 = lean_nat_dec_le(x_137, x_137);
if (x_143 == 0)
{
uint8_t x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_137);
lean_dec(x_124);
lean_dec(x_9);
x_144 = 1;
x_145 = lean_box(x_144);
lean_ctor_set(x_132, 0, x_145);
if (lean_is_scalar(x_128)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_128;
}
lean_ctor_set(x_146, 0, x_132);
lean_ctor_set(x_146, 1, x_133);
return x_146;
}
else
{
size_t x_147; size_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_free_object(x_132);
lean_dec(x_128);
x_147 = 0;
x_148 = lean_usize_of_nat(x_137);
lean_dec(x_137);
x_149 = l_Lake_buildUnlessUpToDate_x3f___rarg___closed__2;
x_150 = l_Lake_buildUnlessUpToDate_x3f___rarg___closed__3;
x_151 = lean_box(0);
x_152 = l_Array_foldlMUnsafe_fold___rarg(x_149, x_150, x_124, x_147, x_148, x_151);
x_153 = lean_apply_3(x_152, x_9, x_135, x_133);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
if (lean_obj_tag(x_154) == 0)
{
uint8_t x_155; 
x_155 = !lean_is_exclusive(x_153);
if (x_155 == 0)
{
lean_object* x_156; uint8_t x_157; 
x_156 = lean_ctor_get(x_153, 0);
lean_dec(x_156);
x_157 = !lean_is_exclusive(x_154);
if (x_157 == 0)
{
lean_object* x_158; uint8_t x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_154, 0);
lean_dec(x_158);
x_159 = 1;
x_160 = lean_box(x_159);
lean_ctor_set(x_154, 0, x_160);
return x_153;
}
else
{
lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; 
x_161 = lean_ctor_get(x_154, 1);
lean_inc(x_161);
lean_dec(x_154);
x_162 = 1;
x_163 = lean_box(x_162);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_161);
lean_ctor_set(x_153, 0, x_164);
return x_153;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_165 = lean_ctor_get(x_153, 1);
lean_inc(x_165);
lean_dec(x_153);
x_166 = lean_ctor_get(x_154, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_167 = x_154;
} else {
 lean_dec_ref(x_154);
 x_167 = lean_box(0);
}
x_168 = 1;
x_169 = lean_box(x_168);
if (lean_is_scalar(x_167)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_167;
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_166);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_165);
return x_171;
}
}
else
{
uint8_t x_172; 
x_172 = !lean_is_exclusive(x_153);
if (x_172 == 0)
{
lean_object* x_173; uint8_t x_174; 
x_173 = lean_ctor_get(x_153, 0);
lean_dec(x_173);
x_174 = !lean_is_exclusive(x_154);
if (x_174 == 0)
{
return x_153;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_154, 0);
x_176 = lean_ctor_get(x_154, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_154);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
lean_ctor_set(x_153, 0, x_177);
return x_153;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_178 = lean_ctor_get(x_153, 1);
lean_inc(x_178);
lean_dec(x_153);
x_179 = lean_ctor_get(x_154, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_154, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_181 = x_154;
} else {
 lean_dec_ref(x_154);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_180);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_178);
return x_183;
}
}
}
else
{
uint8_t x_184; 
x_184 = !lean_is_exclusive(x_153);
if (x_184 == 0)
{
return x_153;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_153, 0);
x_186 = lean_ctor_get(x_153, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_153);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; 
x_188 = lean_ctor_get(x_132, 1);
lean_inc(x_188);
lean_dec(x_132);
x_189 = lean_array_get_size(x_124);
x_190 = lean_unsigned_to_nat(0u);
x_191 = lean_nat_dec_lt(x_190, x_189);
if (x_191 == 0)
{
uint8_t x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_189);
lean_dec(x_124);
lean_dec(x_9);
x_192 = 1;
x_193 = lean_box(x_192);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_188);
if (lean_is_scalar(x_128)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_128;
}
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_133);
return x_195;
}
else
{
uint8_t x_196; 
x_196 = lean_nat_dec_le(x_189, x_189);
if (x_196 == 0)
{
uint8_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_189);
lean_dec(x_124);
lean_dec(x_9);
x_197 = 1;
x_198 = lean_box(x_197);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_188);
if (lean_is_scalar(x_128)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_128;
}
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_133);
return x_200;
}
else
{
size_t x_201; size_t x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_128);
x_201 = 0;
x_202 = lean_usize_of_nat(x_189);
lean_dec(x_189);
x_203 = l_Lake_buildUnlessUpToDate_x3f___rarg___closed__2;
x_204 = l_Lake_buildUnlessUpToDate_x3f___rarg___closed__3;
x_205 = lean_box(0);
x_206 = l_Array_foldlMUnsafe_fold___rarg(x_203, x_204, x_124, x_201, x_202, x_205);
x_207 = lean_apply_3(x_206, x_9, x_188, x_133);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
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
x_211 = lean_ctor_get(x_208, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_212 = x_208;
} else {
 lean_dec_ref(x_208);
 x_212 = lean_box(0);
}
x_213 = 1;
x_214 = lean_box(x_213);
if (lean_is_scalar(x_212)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_212;
}
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_211);
if (lean_is_scalar(x_210)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_210;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_209);
return x_216;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_217 = lean_ctor_get(x_207, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_218 = x_207;
} else {
 lean_dec_ref(x_207);
 x_218 = lean_box(0);
}
x_219 = lean_ctor_get(x_208, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_208, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_221 = x_208;
} else {
 lean_dec_ref(x_208);
 x_221 = lean_box(0);
}
if (lean_is_scalar(x_221)) {
 x_222 = lean_alloc_ctor(1, 2, 0);
} else {
 x_222 = x_221;
}
lean_ctor_set(x_222, 0, x_219);
lean_ctor_set(x_222, 1, x_220);
if (lean_is_scalar(x_218)) {
 x_223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_223 = x_218;
}
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_217);
return x_223;
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_224 = lean_ctor_get(x_207, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_207, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_226 = x_207;
} else {
 lean_dec_ref(x_207);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(1, 2, 0);
} else {
 x_227 = x_226;
}
lean_ctor_set(x_227, 0, x_224);
lean_ctor_set(x_227, 1, x_225);
return x_227;
}
}
}
}
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_298; 
x_252 = lean_ctor_get(x_126, 0);
x_253 = lean_ctor_get(x_126, 1);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_126);
x_298 = lean_unbox(x_252);
lean_dec(x_252);
if (x_298 == 0)
{
lean_object* x_299; lean_object* x_300; 
lean_dec(x_128);
lean_dec(x_124);
x_299 = lean_box(0);
x_300 = l_Lake_buildUnlessUpToDate_x3f___rarg___lambda__1(x_6, x_5, x_4, x_7, x_299, x_9, x_253, x_127);
return x_300;
}
else
{
lean_object* x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; lean_object* x_306; lean_object* x_307; uint8_t x_308; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_301 = lean_ctor_get(x_253, 0);
lean_inc(x_301);
x_302 = lean_ctor_get_uint8(x_253, sizeof(void*)*1);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 x_303 = x_253;
} else {
 lean_dec_ref(x_253);
 x_303 = lean_box(0);
}
x_304 = l_Lake_instOrdJobAction;
x_305 = 1;
x_306 = lean_box(x_302);
x_307 = lean_box(x_305);
x_308 = l_instDecidableRelLe___rarg(x_304, x_306, x_307);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
if (lean_is_scalar(x_303)) {
 x_309 = lean_alloc_ctor(0, 1, 1);
} else {
 x_309 = x_303;
}
lean_ctor_set(x_309, 0, x_301);
lean_ctor_set_uint8(x_309, sizeof(void*)*1, x_302);
x_310 = lean_box(0);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_309);
x_254 = x_311;
x_255 = x_127;
goto block_297;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
if (lean_is_scalar(x_303)) {
 x_312 = lean_alloc_ctor(0, 1, 1);
} else {
 x_312 = x_303;
}
lean_ctor_set(x_312, 0, x_301);
lean_ctor_set_uint8(x_312, sizeof(void*)*1, x_305);
x_313 = lean_box(0);
x_314 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_312);
x_254 = x_314;
x_255 = x_127;
goto block_297;
}
}
block_297:
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; 
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_257 = x_254;
} else {
 lean_dec_ref(x_254);
 x_257 = lean_box(0);
}
x_258 = lean_array_get_size(x_124);
x_259 = lean_unsigned_to_nat(0u);
x_260 = lean_nat_dec_lt(x_259, x_258);
if (x_260 == 0)
{
uint8_t x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_dec(x_258);
lean_dec(x_124);
lean_dec(x_9);
x_261 = 1;
x_262 = lean_box(x_261);
if (lean_is_scalar(x_257)) {
 x_263 = lean_alloc_ctor(0, 2, 0);
} else {
 x_263 = x_257;
}
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_256);
if (lean_is_scalar(x_128)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_128;
}
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_255);
return x_264;
}
else
{
uint8_t x_265; 
x_265 = lean_nat_dec_le(x_258, x_258);
if (x_265 == 0)
{
uint8_t x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_258);
lean_dec(x_124);
lean_dec(x_9);
x_266 = 1;
x_267 = lean_box(x_266);
if (lean_is_scalar(x_257)) {
 x_268 = lean_alloc_ctor(0, 2, 0);
} else {
 x_268 = x_257;
}
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_256);
if (lean_is_scalar(x_128)) {
 x_269 = lean_alloc_ctor(0, 2, 0);
} else {
 x_269 = x_128;
}
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_255);
return x_269;
}
else
{
size_t x_270; size_t x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_dec(x_257);
lean_dec(x_128);
x_270 = 0;
x_271 = lean_usize_of_nat(x_258);
lean_dec(x_258);
x_272 = l_Lake_buildUnlessUpToDate_x3f___rarg___closed__2;
x_273 = l_Lake_buildUnlessUpToDate_x3f___rarg___closed__3;
x_274 = lean_box(0);
x_275 = l_Array_foldlMUnsafe_fold___rarg(x_272, x_273, x_124, x_270, x_271, x_274);
x_276 = lean_apply_3(x_275, x_9, x_256, x_255);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; 
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_279 = x_276;
} else {
 lean_dec_ref(x_276);
 x_279 = lean_box(0);
}
x_280 = lean_ctor_get(x_277, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 x_281 = x_277;
} else {
 lean_dec_ref(x_277);
 x_281 = lean_box(0);
}
x_282 = 1;
x_283 = lean_box(x_282);
if (lean_is_scalar(x_281)) {
 x_284 = lean_alloc_ctor(0, 2, 0);
} else {
 x_284 = x_281;
}
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_280);
if (lean_is_scalar(x_279)) {
 x_285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_285 = x_279;
}
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_278);
return x_285;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_286 = lean_ctor_get(x_276, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_287 = x_276;
} else {
 lean_dec_ref(x_276);
 x_287 = lean_box(0);
}
x_288 = lean_ctor_get(x_277, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_277, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 x_290 = x_277;
} else {
 lean_dec_ref(x_277);
 x_290 = lean_box(0);
}
if (lean_is_scalar(x_290)) {
 x_291 = lean_alloc_ctor(1, 2, 0);
} else {
 x_291 = x_290;
}
lean_ctor_set(x_291, 0, x_288);
lean_ctor_set(x_291, 1, x_289);
if (lean_is_scalar(x_287)) {
 x_292 = lean_alloc_ctor(0, 2, 0);
} else {
 x_292 = x_287;
}
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_286);
return x_292;
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_293 = lean_ctor_get(x_276, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_276, 1);
lean_inc(x_294);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_295 = x_276;
} else {
 lean_dec_ref(x_276);
 x_295 = lean_box(0);
}
if (lean_is_scalar(x_295)) {
 x_296 = lean_alloc_ctor(1, 2, 0);
} else {
 x_296 = x_295;
}
lean_ctor_set(x_296, 0, x_293);
lean_ctor_set(x_296, 1, x_294);
return x_296;
}
}
}
}
}
}
else
{
uint8_t x_315; 
lean_dec(x_124);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_315 = !lean_is_exclusive(x_125);
if (x_315 == 0)
{
lean_object* x_316; uint8_t x_317; 
x_316 = lean_ctor_get(x_125, 0);
lean_dec(x_316);
x_317 = !lean_is_exclusive(x_126);
if (x_317 == 0)
{
return x_125;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_318 = lean_ctor_get(x_126, 0);
x_319 = lean_ctor_get(x_126, 1);
lean_inc(x_319);
lean_inc(x_318);
lean_dec(x_126);
x_320 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_320, 0, x_318);
lean_ctor_set(x_320, 1, x_319);
lean_ctor_set(x_125, 0, x_320);
return x_125;
}
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_321 = lean_ctor_get(x_125, 1);
lean_inc(x_321);
lean_dec(x_125);
x_322 = lean_ctor_get(x_126, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_126, 1);
lean_inc(x_323);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_324 = x_126;
} else {
 lean_dec_ref(x_126);
 x_324 = lean_box(0);
}
if (lean_is_scalar(x_324)) {
 x_325 = lean_alloc_ctor(1, 2, 0);
} else {
 x_325 = x_324;
}
lean_ctor_set(x_325, 0, x_322);
lean_ctor_set(x_325, 1, x_323);
x_326 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_321);
return x_326;
}
}
}
else
{
uint8_t x_327; 
lean_dec(x_124);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_327 = !lean_is_exclusive(x_125);
if (x_327 == 0)
{
return x_125;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_328 = lean_ctor_get(x_125, 0);
x_329 = lean_ctor_get(x_125, 1);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_125);
x_330 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_330, 0, x_328);
lean_ctor_set(x_330, 1, x_329);
return x_330;
}
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_331 = lean_ctor_get(x_14, 0);
lean_inc(x_331);
lean_dec(x_14);
x_332 = lean_ctor_get(x_12, 1);
lean_inc(x_332);
lean_dec(x_12);
x_333 = lean_ctor_get(x_331, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_331, 1);
lean_inc(x_334);
lean_dec(x_331);
x_335 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_335, 0, x_333);
lean_inc(x_4);
x_336 = l_Lake_checkHashUpToDate___rarg(x_1, x_2, x_3, x_4, x_335, x_8, x_9, x_332, x_13);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; 
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; uint8_t x_387; 
x_338 = lean_ctor_get(x_336, 1);
lean_inc(x_338);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 x_339 = x_336;
} else {
 lean_dec_ref(x_336);
 x_339 = lean_box(0);
}
x_340 = lean_ctor_get(x_337, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_337, 1);
lean_inc(x_341);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_342 = x_337;
} else {
 lean_dec_ref(x_337);
 x_342 = lean_box(0);
}
x_387 = lean_unbox(x_340);
lean_dec(x_340);
if (x_387 == 0)
{
lean_object* x_388; lean_object* x_389; 
lean_dec(x_342);
lean_dec(x_339);
lean_dec(x_334);
x_388 = lean_box(0);
x_389 = l_Lake_buildUnlessUpToDate_x3f___rarg___lambda__1(x_6, x_5, x_4, x_7, x_388, x_9, x_341, x_338);
return x_389;
}
else
{
lean_object* x_390; uint8_t x_391; lean_object* x_392; lean_object* x_393; uint8_t x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_390 = lean_ctor_get(x_341, 0);
lean_inc(x_390);
x_391 = lean_ctor_get_uint8(x_341, sizeof(void*)*1);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 x_392 = x_341;
} else {
 lean_dec_ref(x_341);
 x_392 = lean_box(0);
}
x_393 = l_Lake_instOrdJobAction;
x_394 = 1;
x_395 = lean_box(x_391);
x_396 = lean_box(x_394);
x_397 = l_instDecidableRelLe___rarg(x_393, x_395, x_396);
if (x_397 == 0)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; 
if (lean_is_scalar(x_392)) {
 x_398 = lean_alloc_ctor(0, 1, 1);
} else {
 x_398 = x_392;
}
lean_ctor_set(x_398, 0, x_390);
lean_ctor_set_uint8(x_398, sizeof(void*)*1, x_391);
x_399 = lean_box(0);
if (lean_is_scalar(x_342)) {
 x_400 = lean_alloc_ctor(0, 2, 0);
} else {
 x_400 = x_342;
}
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_398);
x_343 = x_400;
x_344 = x_338;
goto block_386;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; 
if (lean_is_scalar(x_392)) {
 x_401 = lean_alloc_ctor(0, 1, 1);
} else {
 x_401 = x_392;
}
lean_ctor_set(x_401, 0, x_390);
lean_ctor_set_uint8(x_401, sizeof(void*)*1, x_394);
x_402 = lean_box(0);
if (lean_is_scalar(x_342)) {
 x_403 = lean_alloc_ctor(0, 2, 0);
} else {
 x_403 = x_342;
}
lean_ctor_set(x_403, 0, x_402);
lean_ctor_set(x_403, 1, x_401);
x_343 = x_403;
x_344 = x_338;
goto block_386;
}
}
block_386:
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; 
x_345 = lean_ctor_get(x_343, 1);
lean_inc(x_345);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 x_346 = x_343;
} else {
 lean_dec_ref(x_343);
 x_346 = lean_box(0);
}
x_347 = lean_array_get_size(x_334);
x_348 = lean_unsigned_to_nat(0u);
x_349 = lean_nat_dec_lt(x_348, x_347);
if (x_349 == 0)
{
uint8_t x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
lean_dec(x_347);
lean_dec(x_334);
lean_dec(x_9);
x_350 = 1;
x_351 = lean_box(x_350);
if (lean_is_scalar(x_346)) {
 x_352 = lean_alloc_ctor(0, 2, 0);
} else {
 x_352 = x_346;
}
lean_ctor_set(x_352, 0, x_351);
lean_ctor_set(x_352, 1, x_345);
if (lean_is_scalar(x_339)) {
 x_353 = lean_alloc_ctor(0, 2, 0);
} else {
 x_353 = x_339;
}
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_344);
return x_353;
}
else
{
uint8_t x_354; 
x_354 = lean_nat_dec_le(x_347, x_347);
if (x_354 == 0)
{
uint8_t x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
lean_dec(x_347);
lean_dec(x_334);
lean_dec(x_9);
x_355 = 1;
x_356 = lean_box(x_355);
if (lean_is_scalar(x_346)) {
 x_357 = lean_alloc_ctor(0, 2, 0);
} else {
 x_357 = x_346;
}
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_345);
if (lean_is_scalar(x_339)) {
 x_358 = lean_alloc_ctor(0, 2, 0);
} else {
 x_358 = x_339;
}
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set(x_358, 1, x_344);
return x_358;
}
else
{
size_t x_359; size_t x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
lean_dec(x_346);
lean_dec(x_339);
x_359 = 0;
x_360 = lean_usize_of_nat(x_347);
lean_dec(x_347);
x_361 = l_Lake_buildUnlessUpToDate_x3f___rarg___closed__2;
x_362 = l_Lake_buildUnlessUpToDate_x3f___rarg___closed__3;
x_363 = lean_box(0);
x_364 = l_Array_foldlMUnsafe_fold___rarg(x_361, x_362, x_334, x_359, x_360, x_363);
x_365 = lean_apply_3(x_364, x_9, x_345, x_344);
if (lean_obj_tag(x_365) == 0)
{
lean_object* x_366; 
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; uint8_t x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_367 = lean_ctor_get(x_365, 1);
lean_inc(x_367);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 x_368 = x_365;
} else {
 lean_dec_ref(x_365);
 x_368 = lean_box(0);
}
x_369 = lean_ctor_get(x_366, 1);
lean_inc(x_369);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 x_370 = x_366;
} else {
 lean_dec_ref(x_366);
 x_370 = lean_box(0);
}
x_371 = 1;
x_372 = lean_box(x_371);
if (lean_is_scalar(x_370)) {
 x_373 = lean_alloc_ctor(0, 2, 0);
} else {
 x_373 = x_370;
}
lean_ctor_set(x_373, 0, x_372);
lean_ctor_set(x_373, 1, x_369);
if (lean_is_scalar(x_368)) {
 x_374 = lean_alloc_ctor(0, 2, 0);
} else {
 x_374 = x_368;
}
lean_ctor_set(x_374, 0, x_373);
lean_ctor_set(x_374, 1, x_367);
return x_374;
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_375 = lean_ctor_get(x_365, 1);
lean_inc(x_375);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 x_376 = x_365;
} else {
 lean_dec_ref(x_365);
 x_376 = lean_box(0);
}
x_377 = lean_ctor_get(x_366, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_366, 1);
lean_inc(x_378);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 x_379 = x_366;
} else {
 lean_dec_ref(x_366);
 x_379 = lean_box(0);
}
if (lean_is_scalar(x_379)) {
 x_380 = lean_alloc_ctor(1, 2, 0);
} else {
 x_380 = x_379;
}
lean_ctor_set(x_380, 0, x_377);
lean_ctor_set(x_380, 1, x_378);
if (lean_is_scalar(x_376)) {
 x_381 = lean_alloc_ctor(0, 2, 0);
} else {
 x_381 = x_376;
}
lean_ctor_set(x_381, 0, x_380);
lean_ctor_set(x_381, 1, x_375);
return x_381;
}
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_382 = lean_ctor_get(x_365, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_365, 1);
lean_inc(x_383);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 x_384 = x_365;
} else {
 lean_dec_ref(x_365);
 x_384 = lean_box(0);
}
if (lean_is_scalar(x_384)) {
 x_385 = lean_alloc_ctor(1, 2, 0);
} else {
 x_385 = x_384;
}
lean_ctor_set(x_385, 0, x_382);
lean_ctor_set(x_385, 1, x_383);
return x_385;
}
}
}
}
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
lean_dec(x_334);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_404 = lean_ctor_get(x_336, 1);
lean_inc(x_404);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 x_405 = x_336;
} else {
 lean_dec_ref(x_336);
 x_405 = lean_box(0);
}
x_406 = lean_ctor_get(x_337, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_337, 1);
lean_inc(x_407);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_408 = x_337;
} else {
 lean_dec_ref(x_337);
 x_408 = lean_box(0);
}
if (lean_is_scalar(x_408)) {
 x_409 = lean_alloc_ctor(1, 2, 0);
} else {
 x_409 = x_408;
}
lean_ctor_set(x_409, 0, x_406);
lean_ctor_set(x_409, 1, x_407);
if (lean_is_scalar(x_405)) {
 x_410 = lean_alloc_ctor(0, 2, 0);
} else {
 x_410 = x_405;
}
lean_ctor_set(x_410, 0, x_409);
lean_ctor_set(x_410, 1, x_404);
return x_410;
}
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
lean_dec(x_334);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_411 = lean_ctor_get(x_336, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_336, 1);
lean_inc(x_412);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 x_413 = x_336;
} else {
 lean_dec_ref(x_336);
 x_413 = lean_box(0);
}
if (lean_is_scalar(x_413)) {
 x_414 = lean_alloc_ctor(1, 2, 0);
} else {
 x_414 = x_413;
}
lean_ctor_set(x_414, 0, x_411);
lean_ctor_set(x_414, 1, x_412);
return x_414;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_buildUnlessUpToDate_x3f___rarg___boxed), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Lake_buildUnlessUpToDate_x3f___rarg___lambda__1(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_buildUnlessUpToDate_x3f___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_7);
lean_dec(x_7);
x_13 = l_Lake_buildUnlessUpToDate_x3f___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_12, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_buildUnlessUpToDate_x3f___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_13, 0, x_18);
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_box(0);
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
x_25 = lean_box(0);
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
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_12);
if (x_40 == 0)
{
return x_12;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_12, 0);
x_42 = lean_ctor_get(x_12, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_12);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_buildUnlessUpToDate___rarg___boxed), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_7);
lean_dec(x_7);
x_13 = l_Lake_buildUnlessUpToDate___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_12, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l_Lake_cacheFileHash___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(".hash", 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheFileHash(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_computeFileHash(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lake_cacheFileHash___closed__1;
x_7 = lean_string_append(x_1, x_6);
lean_inc(x_7);
x_8 = l_Lake_createParentDirs(x_7, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint64_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_11 = lean_uint64_to_nat(x_10);
x_12 = l___private_Init_Data_Repr_0__Nat_reprFast(x_11);
x_13 = l_IO_FS_writeFile(x_7, x_12, x_9);
lean_dec(x_12);
lean_dec(x_7);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_7);
lean_dec(x_4);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
else
{
uint8_t x_18; 
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
return x_3;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_3, 0);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_3);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_clearFileHash(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lake_cacheFileHash___closed__1;
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
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_5, 0);
lean_dec(x_14);
return x_5;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_175; 
x_175 = !lean_is_exclusive(x_5);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_5, 0);
x_177 = l_Lake_computeFileHash(x_1, x_6);
if (lean_obj_tag(x_177) == 0)
{
uint8_t x_178; 
x_178 = !lean_is_exclusive(x_177);
if (x_178 == 0)
{
lean_object* x_179; 
x_179 = lean_ctor_get(x_177, 1);
lean_ctor_set(x_177, 1, x_5);
x_7 = x_177;
x_8 = x_179;
goto block_174;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_177, 0);
x_181 = lean_ctor_get(x_177, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_177);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_5);
x_7 = x_182;
x_8 = x_181;
goto block_174;
}
}
else
{
uint8_t x_183; 
x_183 = !lean_is_exclusive(x_177);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_184 = lean_ctor_get(x_177, 0);
x_185 = lean_ctor_get(x_177, 1);
x_186 = lean_io_error_to_string(x_184);
x_187 = 3;
x_188 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set_uint8(x_188, sizeof(void*)*1, x_187);
x_189 = lean_array_get_size(x_176);
x_190 = lean_array_push(x_176, x_188);
lean_ctor_set(x_5, 0, x_190);
lean_ctor_set(x_177, 1, x_5);
lean_ctor_set(x_177, 0, x_189);
x_7 = x_177;
x_8 = x_185;
goto block_174;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_191 = lean_ctor_get(x_177, 0);
x_192 = lean_ctor_get(x_177, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_177);
x_193 = lean_io_error_to_string(x_191);
x_194 = 3;
x_195 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set_uint8(x_195, sizeof(void*)*1, x_194);
x_196 = lean_array_get_size(x_176);
x_197 = lean_array_push(x_176, x_195);
lean_ctor_set(x_5, 0, x_197);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_5);
x_7 = x_198;
x_8 = x_192;
goto block_174;
}
}
}
else
{
lean_object* x_199; uint8_t x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_5, 0);
x_200 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
lean_inc(x_199);
lean_dec(x_5);
x_201 = l_Lake_computeFileHash(x_1, x_6);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_204 = x_201;
} else {
 lean_dec_ref(x_201);
 x_204 = lean_box(0);
}
x_205 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_205, 0, x_199);
lean_ctor_set_uint8(x_205, sizeof(void*)*1, x_200);
if (lean_is_scalar(x_204)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_204;
}
lean_ctor_set(x_206, 0, x_202);
lean_ctor_set(x_206, 1, x_205);
x_7 = x_206;
x_8 = x_203;
goto block_174;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_207 = lean_ctor_get(x_201, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_201, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_209 = x_201;
} else {
 lean_dec_ref(x_201);
 x_209 = lean_box(0);
}
x_210 = lean_io_error_to_string(x_207);
x_211 = 3;
x_212 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set_uint8(x_212, sizeof(void*)*1, x_211);
x_213 = lean_array_get_size(x_199);
x_214 = lean_array_push(x_199, x_212);
x_215 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set_uint8(x_215, sizeof(void*)*1, x_200);
if (lean_is_scalar(x_209)) {
 x_216 = lean_alloc_ctor(1, 2, 0);
} else {
 x_216 = x_209;
}
lean_ctor_set(x_216, 0, x_213);
lean_ctor_set(x_216, 1, x_215);
x_7 = x_216;
x_8 = x_208;
goto block_174;
}
}
block_174:
{
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_90; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
x_90 = !lean_is_exclusive(x_11);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_11, 0);
lean_inc(x_2);
x_92 = l_Lake_createParentDirs(x_2, x_8);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
lean_ctor_set(x_7, 0, x_93);
x_12 = x_7;
x_13 = x_94;
goto block_89;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_95 = lean_ctor_get(x_92, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_92, 1);
lean_inc(x_96);
lean_dec(x_92);
x_97 = lean_io_error_to_string(x_95);
x_98 = 3;
x_99 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set_uint8(x_99, sizeof(void*)*1, x_98);
x_100 = lean_array_get_size(x_91);
x_101 = lean_array_push(x_91, x_99);
lean_ctor_set(x_11, 0, x_101);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_100);
x_12 = x_7;
x_13 = x_96;
goto block_89;
}
}
else
{
lean_object* x_102; uint8_t x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_11, 0);
x_103 = lean_ctor_get_uint8(x_11, sizeof(void*)*1);
lean_inc(x_102);
lean_dec(x_11);
lean_inc(x_2);
x_104 = l_Lake_createParentDirs(x_2, x_8);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_107, 0, x_102);
lean_ctor_set_uint8(x_107, sizeof(void*)*1, x_103);
lean_ctor_set(x_7, 1, x_107);
lean_ctor_set(x_7, 0, x_105);
x_12 = x_7;
x_13 = x_106;
goto block_89;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_108 = lean_ctor_get(x_104, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_104, 1);
lean_inc(x_109);
lean_dec(x_104);
x_110 = lean_io_error_to_string(x_108);
x_111 = 3;
x_112 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set_uint8(x_112, sizeof(void*)*1, x_111);
x_113 = lean_array_get_size(x_102);
x_114 = lean_array_push(x_102, x_112);
x_115 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set_uint8(x_115, sizeof(void*)*1, x_103);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_115);
lean_ctor_set(x_7, 0, x_113);
x_12 = x_7;
x_13 = x_109;
goto block_89;
}
}
block_89:
{
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
x_17 = lean_unbox_uint64(x_10);
x_18 = lean_uint64_to_nat(x_17);
x_19 = l___private_Init_Data_Repr_0__Nat_reprFast(x_18);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = l_IO_FS_writeFile(x_2, x_19, x_13);
lean_dec(x_19);
lean_dec(x_2);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_22, 0, x_12);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
lean_ctor_set(x_12, 0, x_10);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_12);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_10);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_io_error_to_string(x_28);
x_30 = 3;
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_30);
x_32 = lean_array_get_size(x_21);
x_33 = lean_array_push(x_21, x_31);
lean_ctor_set(x_15, 0, x_33);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_32);
lean_ctor_set_tag(x_22, 0);
lean_ctor_set(x_22, 0, x_12);
return x_22;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_22, 0);
x_35 = lean_ctor_get(x_22, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_22);
x_36 = lean_io_error_to_string(x_34);
x_37 = 3;
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_37);
x_39 = lean_array_get_size(x_21);
x_40 = lean_array_push(x_21, x_38);
lean_ctor_set(x_15, 0, x_40);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_12);
lean_ctor_set(x_41, 1, x_35);
return x_41;
}
}
}
else
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_15, 0);
x_43 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
lean_inc(x_42);
lean_dec(x_15);
x_44 = l_IO_FS_writeFile(x_2, x_19, x_13);
lean_dec(x_19);
lean_dec(x_2);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
x_47 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_43);
lean_ctor_set(x_12, 1, x_47);
lean_ctor_set(x_12, 0, x_10);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_12);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_10);
x_49 = lean_ctor_get(x_44, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_51 = x_44;
} else {
 lean_dec_ref(x_44);
 x_51 = lean_box(0);
}
x_52 = lean_io_error_to_string(x_49);
x_53 = 3;
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_53);
x_55 = lean_array_get_size(x_42);
x_56 = lean_array_push(x_42, x_54);
x_57 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_43);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_57);
lean_ctor_set(x_12, 0, x_55);
if (lean_is_scalar(x_51)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_51;
 lean_ctor_set_tag(x_58, 0);
}
lean_ctor_set(x_58, 0, x_12);
lean_ctor_set(x_58, 1, x_50);
return x_58;
}
}
}
else
{
lean_object* x_59; uint64_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; 
x_59 = lean_ctor_get(x_12, 1);
lean_inc(x_59);
lean_dec(x_12);
x_60 = lean_unbox_uint64(x_10);
x_61 = lean_uint64_to_nat(x_60);
x_62 = l___private_Init_Data_Repr_0__Nat_reprFast(x_61);
x_63 = lean_ctor_get(x_59, 0);
lean_inc(x_63);
x_64 = lean_ctor_get_uint8(x_59, sizeof(void*)*1);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_65 = x_59;
} else {
 lean_dec_ref(x_59);
 x_65 = lean_box(0);
}
x_66 = l_IO_FS_writeFile(x_2, x_62, x_13);
lean_dec(x_62);
lean_dec(x_2);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
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
if (lean_is_scalar(x_65)) {
 x_69 = lean_alloc_ctor(0, 1, 1);
} else {
 x_69 = x_65;
}
lean_ctor_set(x_69, 0, x_63);
lean_ctor_set_uint8(x_69, sizeof(void*)*1, x_64);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_10);
lean_ctor_set(x_70, 1, x_69);
if (lean_is_scalar(x_68)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_68;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_67);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_10);
x_72 = lean_ctor_get(x_66, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_66, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_74 = x_66;
} else {
 lean_dec_ref(x_66);
 x_74 = lean_box(0);
}
x_75 = lean_io_error_to_string(x_72);
x_76 = 3;
x_77 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set_uint8(x_77, sizeof(void*)*1, x_76);
x_78 = lean_array_get_size(x_63);
x_79 = lean_array_push(x_63, x_77);
if (lean_is_scalar(x_65)) {
 x_80 = lean_alloc_ctor(0, 1, 1);
} else {
 x_80 = x_65;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_64);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_80);
if (lean_is_scalar(x_74)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_74;
 lean_ctor_set_tag(x_82, 0);
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_73);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_10);
lean_dec(x_2);
x_83 = !lean_is_exclusive(x_12);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_12);
lean_ctor_set(x_84, 1, x_13);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_12, 0);
x_86 = lean_ctor_get(x_12, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_12);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_13);
return x_88;
}
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; 
x_116 = lean_ctor_get(x_7, 0);
x_117 = lean_ctor_get(x_7, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_7);
x_151 = lean_ctor_get(x_117, 0);
lean_inc(x_151);
x_152 = lean_ctor_get_uint8(x_117, sizeof(void*)*1);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 x_153 = x_117;
} else {
 lean_dec_ref(x_117);
 x_153 = lean_box(0);
}
lean_inc(x_2);
x_154 = l_Lake_createParentDirs(x_2, x_8);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
if (lean_is_scalar(x_153)) {
 x_157 = lean_alloc_ctor(0, 1, 1);
} else {
 x_157 = x_153;
}
lean_ctor_set(x_157, 0, x_151);
lean_ctor_set_uint8(x_157, sizeof(void*)*1, x_152);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_157);
x_118 = x_158;
x_119 = x_156;
goto block_150;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_159 = lean_ctor_get(x_154, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_154, 1);
lean_inc(x_160);
lean_dec(x_154);
x_161 = lean_io_error_to_string(x_159);
x_162 = 3;
x_163 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set_uint8(x_163, sizeof(void*)*1, x_162);
x_164 = lean_array_get_size(x_151);
x_165 = lean_array_push(x_151, x_163);
if (lean_is_scalar(x_153)) {
 x_166 = lean_alloc_ctor(0, 1, 1);
} else {
 x_166 = x_153;
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set_uint8(x_166, sizeof(void*)*1, x_152);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_166);
x_118 = x_167;
x_119 = x_160;
goto block_150;
}
block_150:
{
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_120; lean_object* x_121; uint64_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; 
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
x_122 = lean_unbox_uint64(x_116);
x_123 = lean_uint64_to_nat(x_122);
x_124 = l___private_Init_Data_Repr_0__Nat_reprFast(x_123);
x_125 = lean_ctor_get(x_120, 0);
lean_inc(x_125);
x_126 = lean_ctor_get_uint8(x_120, sizeof(void*)*1);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 x_127 = x_120;
} else {
 lean_dec_ref(x_120);
 x_127 = lean_box(0);
}
x_128 = l_IO_FS_writeFile(x_2, x_124, x_119);
lean_dec(x_124);
lean_dec(x_2);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_130 = x_128;
} else {
 lean_dec_ref(x_128);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_131 = lean_alloc_ctor(0, 1, 1);
} else {
 x_131 = x_127;
}
lean_ctor_set(x_131, 0, x_125);
lean_ctor_set_uint8(x_131, sizeof(void*)*1, x_126);
if (lean_is_scalar(x_121)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_121;
}
lean_ctor_set(x_132, 0, x_116);
lean_ctor_set(x_132, 1, x_131);
if (lean_is_scalar(x_130)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_130;
}
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_129);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_116);
x_134 = lean_ctor_get(x_128, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_128, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_136 = x_128;
} else {
 lean_dec_ref(x_128);
 x_136 = lean_box(0);
}
x_137 = lean_io_error_to_string(x_134);
x_138 = 3;
x_139 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set_uint8(x_139, sizeof(void*)*1, x_138);
x_140 = lean_array_get_size(x_125);
x_141 = lean_array_push(x_125, x_139);
if (lean_is_scalar(x_127)) {
 x_142 = lean_alloc_ctor(0, 1, 1);
} else {
 x_142 = x_127;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set_uint8(x_142, sizeof(void*)*1, x_126);
if (lean_is_scalar(x_121)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_121;
 lean_ctor_set_tag(x_143, 1);
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_142);
if (lean_is_scalar(x_136)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_136;
 lean_ctor_set_tag(x_144, 0);
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_135);
return x_144;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_116);
lean_dec(x_2);
x_145 = lean_ctor_get(x_118, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_118, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_147 = x_118;
} else {
 lean_dec_ref(x_118);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_146);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_119);
return x_149;
}
}
}
}
else
{
uint8_t x_168; 
lean_dec(x_2);
x_168 = !lean_is_exclusive(x_7);
if (x_168 == 0)
{
lean_object* x_169; 
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_7);
lean_ctor_set(x_169, 1, x_8);
return x_169;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_170 = lean_ctor_get(x_7, 0);
x_171 = lean_ctor_get(x_7, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_7);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_8);
return x_173;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = l_Lake_cacheFileHash___closed__1;
lean_inc(x_1);
x_6 = lean_string_append(x_1, x_5);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*1 + 1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = l_Lake_fetchFileHash___lambda__1(x_1, x_6, x_9, x_2, x_3, x_4);
lean_dec(x_1);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lake_Hash_load_x3f(x_6, x_4);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 1);
lean_free_object(x_12);
x_16 = lean_box(0);
x_17 = l_Lake_fetchFileHash___lambda__1(x_1, x_6, x_16, x_2, x_3, x_15);
lean_dec(x_1);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_6);
lean_dec(x_1);
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
lean_ctor_set(x_12, 0, x_19);
return x_12;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_box(0);
x_23 = l_Lake_fetchFileHash___lambda__1(x_1, x_6, x_22, x_2, x_3, x_21);
lean_dec(x_1);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_6);
lean_dec(x_1);
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_3);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
return x_26;
}
}
}
else
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_3, 0);
x_28 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
lean_inc(x_27);
lean_dec(x_3);
x_29 = l_Lake_Hash_load_x3f(x_6, x_4);
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
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_32);
x_34 = lean_box(0);
x_35 = l_Lake_fetchFileHash___lambda__1(x_1, x_6, x_34, x_2, x_33, x_31);
lean_dec(x_1);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_6);
lean_dec(x_1);
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
if (lean_is_scalar(x_32)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_32;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_31);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_fetchFileHash___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_fetchFileHash(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_1);
x_5 = l_Lake_fetchFileHash(x_1, x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_io_metadata(x_1, x_8);
lean_dec(x_1);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_6, 0, x_18);
lean_ctor_set(x_14, 0, x_6);
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
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_6, 0, x_22);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_10);
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_io_error_to_string(x_25);
x_27 = 3;
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = lean_array_get_size(x_13);
x_30 = lean_array_push(x_13, x_28);
lean_ctor_set(x_7, 0, x_30);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_29);
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 0, x_6);
return x_14;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_14, 0);
x_32 = lean_ctor_get(x_14, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_14);
x_33 = lean_io_error_to_string(x_31);
x_34 = 3;
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
x_36 = lean_array_get_size(x_13);
x_37 = lean_array_push(x_13, x_35);
lean_ctor_set(x_7, 0, x_37);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_6);
lean_ctor_set(x_38, 1, x_32);
return x_38;
}
}
}
else
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_7, 0);
x_40 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
lean_inc(x_39);
lean_dec(x_7);
x_41 = lean_io_metadata(x_1, x_8);
lean_dec(x_1);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
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
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_40);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_10);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set(x_6, 1, x_46);
lean_ctor_set(x_6, 0, x_47);
if (lean_is_scalar(x_44)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_44;
}
lean_ctor_set(x_48, 0, x_6);
lean_ctor_set(x_48, 1, x_43);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_10);
x_49 = lean_ctor_get(x_41, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_41, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_51 = x_41;
} else {
 lean_dec_ref(x_41);
 x_51 = lean_box(0);
}
x_52 = lean_io_error_to_string(x_49);
x_53 = 3;
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_53);
x_55 = lean_array_get_size(x_39);
x_56 = lean_array_push(x_39, x_54);
x_57 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_40);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 1, x_57);
lean_ctor_set(x_6, 0, x_55);
if (lean_is_scalar(x_51)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_51;
 lean_ctor_set_tag(x_58, 0);
}
lean_ctor_set(x_58, 0, x_6);
lean_ctor_set(x_58, 1, x_50);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_6, 0);
lean_inc(x_59);
lean_dec(x_6);
x_60 = lean_ctor_get(x_7, 0);
lean_inc(x_60);
x_61 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_62 = x_7;
} else {
 lean_dec_ref(x_7);
 x_62 = lean_box(0);
}
x_63 = lean_io_metadata(x_1, x_8);
lean_dec(x_1);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
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
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 1, 1);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_60);
lean_ctor_set_uint8(x_68, sizeof(void*)*1, x_61);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_59);
lean_ctor_set(x_69, 1, x_67);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
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
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_59);
x_72 = lean_ctor_get(x_63, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_63, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_74 = x_63;
} else {
 lean_dec_ref(x_63);
 x_74 = lean_box(0);
}
x_75 = lean_io_error_to_string(x_72);
x_76 = 3;
x_77 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set_uint8(x_77, sizeof(void*)*1, x_76);
x_78 = lean_array_get_size(x_60);
x_79 = lean_array_push(x_60, x_77);
if (lean_is_scalar(x_62)) {
 x_80 = lean_alloc_ctor(0, 1, 1);
} else {
 x_80 = x_62;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_61);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_80);
if (lean_is_scalar(x_74)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_74;
 lean_ctor_set_tag(x_82, 0);
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_73);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_5);
if (x_83 == 0)
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_5, 0);
lean_dec(x_84);
x_85 = !lean_is_exclusive(x_6);
if (x_85 == 0)
{
return x_5;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_6, 0);
x_87 = lean_ctor_get(x_6, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_6);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
lean_ctor_set(x_5, 0, x_88);
return x_5;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_89 = lean_ctor_get(x_5, 1);
lean_inc(x_89);
lean_dec(x_5);
x_90 = lean_ctor_get(x_6, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_6, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_92 = x_6;
} else {
 lean_dec_ref(x_6);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_89);
return x_94;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_fetchFileTrace(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_3);
x_6 = lean_apply_3(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_apply_4(x_2, x_9, x_3, x_10, x_8);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_6, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
return x_6;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_7);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_6, 0, x_17);
return x_6;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_dec(x_6);
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_21 = x_7;
} else {
 lean_dec_ref(x_7);
 x_21 = lean_box(0);
}
if (lean_is_scalar(x_21)) {
 x_22 = lean_alloc_ctor(1, 2, 0);
} else {
 x_22 = x_21;
}
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_6);
if (x_24 == 0)
{
return x_6;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_6, 0);
x_26 = lean_ctor_get(x_6, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_6);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lake_MTime_instOrd;
x_9 = l_instDecidableRelLt___rarg(x_8, x_2, x_7);
x_10 = lean_box(x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lake_MTime_instOrd;
x_15 = l_instDecidableRelLt___rarg(x_14, x_2, x_13);
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_4);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_4, 0);
lean_dec(x_19);
x_20 = 0;
x_21 = lean_box(x_20);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_21);
return x_4;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
lean_dec(x_4);
x_23 = 0;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lake_buildFileUnlessUpToDate___spec__5(lean_object* x_1, lean_object* x_2) {
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
lean_dec(x_2);
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
lean_dec(x_1);
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_unbox_uint64(x_6);
lean_dec(x_6);
x_9 = lean_unbox_uint64(x_7);
lean_dec(x_7);
x_10 = lean_uint64_dec_eq(x_8, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___at_Lake_buildFileUnlessUpToDate___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_dec(x_10);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lake_buildFileUnlessUpToDate___spec__5(x_11, x_3);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*1);
if (x_14 == 0)
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
x_15 = 0;
x_16 = lean_box(x_15);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_7);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_6);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__3(x_1, x_4, x_7);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_21);
lean_ctor_set(x_19, 0, x_2);
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
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_6, 0);
x_26 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
lean_inc(x_25);
lean_dec(x_6);
x_27 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__3(x_1, x_4, x_7);
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
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_26);
lean_ctor_set(x_2, 1, x_31);
lean_ctor_set(x_2, 0, x_28);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_6);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = l_System_FilePath_pathExists(x_1, x_7);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_36);
lean_ctor_set(x_34, 0, x_2);
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
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_2);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_6, 0);
x_41 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
lean_inc(x_40);
lean_dec(x_6);
x_42 = l_System_FilePath_pathExists(x_1, x_7);
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
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_41);
lean_ctor_set(x_2, 1, x_46);
lean_ctor_set(x_2, 0, x_43);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_2);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_2, 0);
lean_inc(x_48);
lean_dec(x_2);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lake_buildFileUnlessUpToDate___spec__5(x_49, x_3);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_5, 0);
x_52 = lean_ctor_get_uint8(x_51, sizeof(void*)*1);
if (x_52 == 0)
{
uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_4);
x_53 = 0;
x_54 = lean_box(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_6);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_7);
return x_56;
}
else
{
lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_57 = lean_ctor_get(x_6, 0);
lean_inc(x_57);
x_58 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_59 = x_6;
} else {
 lean_dec_ref(x_6);
 x_59 = lean_box(0);
}
x_60 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__3(x_1, x_4, x_7);
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
if (lean_is_scalar(x_59)) {
 x_64 = lean_alloc_ctor(0, 1, 1);
} else {
 x_64 = x_59;
}
lean_ctor_set(x_64, 0, x_57);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_58);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_61);
lean_ctor_set(x_65, 1, x_64);
if (lean_is_scalar(x_63)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_63;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_62);
return x_66;
}
}
else
{
lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_4);
x_67 = lean_ctor_get(x_6, 0);
lean_inc(x_67);
x_68 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_69 = x_6;
} else {
 lean_dec_ref(x_6);
 x_69 = lean_box(0);
}
x_70 = l_System_FilePath_pathExists(x_1, x_7);
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
if (lean_is_scalar(x_69)) {
 x_74 = lean_alloc_ctor(0, 1, 1);
} else {
 x_74 = x_69;
}
lean_ctor_set(x_74, 0, x_67);
lean_ctor_set_uint8(x_74, sizeof(void*)*1, x_68);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_71);
lean_ctor_set(x_75, 1, x_74);
if (lean_is_scalar(x_73)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_73;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_72);
return x_76;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate___spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_2, x_3);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_4);
x_9 = lean_array_uget(x_1, x_2);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_array_push(x_11, x_9);
lean_ctor_set(x_6, 0, x_12);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_15 = lean_box(0);
x_2 = x_14;
x_4 = x_15;
goto _start;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
lean_inc(x_17);
lean_dec(x_6);
x_19 = lean_array_push(x_17, x_9);
x_20 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_18);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_23 = lean_box(0);
x_2 = x_22;
x_4 = x_23;
x_6 = x_20;
goto _start;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_6);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_7);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_buildFileUnlessUpToDate___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = l_Lake_clearFileHash(x_1, x_5);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_4);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_io_error_to_string(x_17);
x_19 = 3;
x_20 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_19);
x_21 = lean_array_get_size(x_7);
x_22 = lean_array_push(x_7, x_20);
lean_ctor_set(x_4, 0, x_22);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_4);
lean_ctor_set_tag(x_8, 0);
lean_ctor_set(x_8, 0, x_23);
return x_8;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_8, 0);
x_25 = lean_ctor_get(x_8, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_8);
x_26 = lean_io_error_to_string(x_24);
x_27 = 3;
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = lean_array_get_size(x_7);
x_30 = lean_array_push(x_7, x_28);
lean_ctor_set(x_4, 0, x_30);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_4);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_25);
return x_32;
}
}
}
else
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_4, 0);
x_34 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_inc(x_33);
lean_dec(x_4);
x_35 = l_Lake_clearFileHash(x_1, x_5);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
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
x_39 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_34);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_39);
if (lean_is_scalar(x_38)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_38;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_42 = lean_ctor_get(x_35, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_35, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_44 = x_35;
} else {
 lean_dec_ref(x_35);
 x_44 = lean_box(0);
}
x_45 = lean_io_error_to_string(x_42);
x_46 = 3;
x_47 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_46);
x_48 = lean_array_get_size(x_33);
x_49 = lean_array_push(x_33, x_47);
x_50 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_34);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
if (lean_is_scalar(x_44)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_44;
 lean_ctor_set_tag(x_52, 0);
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_43);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_buildFileUnlessUpToDate___spec__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_135 = l_Lake_buildUnlessUpToDate_x3f___rarg___lambda__1___closed__1;
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
x_163 = l_Lake_buildUnlessUpToDate_x3f___rarg___lambda__1___closed__1;
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
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_buildFileUnlessUpToDate___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_328; 
x_11 = lean_alloc_closure((void*)(l_Lake_buildUnlessUpToDate_x3f___at_Lake_buildFileUnlessUpToDate___spec__2___lambda__1___boxed), 5, 1);
lean_closure_set(x_11, 0, x_1);
x_328 = !lean_is_exclusive(x_9);
if (x_328 == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; uint8_t x_333; 
x_329 = lean_ctor_get(x_9, 0);
x_330 = l_Lake_readTraceFile_x3f(x_5, x_329, x_10);
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_330, 1);
lean_inc(x_332);
lean_dec(x_330);
x_333 = !lean_is_exclusive(x_331);
if (x_333 == 0)
{
lean_object* x_334; 
x_334 = lean_ctor_get(x_331, 1);
lean_ctor_set(x_9, 0, x_334);
lean_ctor_set(x_331, 1, x_9);
x_12 = x_331;
x_13 = x_332;
goto block_327;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_335 = lean_ctor_get(x_331, 0);
x_336 = lean_ctor_get(x_331, 1);
lean_inc(x_336);
lean_inc(x_335);
lean_dec(x_331);
lean_ctor_set(x_9, 0, x_336);
x_337 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_337, 0, x_335);
lean_ctor_set(x_337, 1, x_9);
x_12 = x_337;
x_13 = x_332;
goto block_327;
}
}
else
{
lean_object* x_338; uint8_t x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_338 = lean_ctor_get(x_9, 0);
x_339 = lean_ctor_get_uint8(x_9, sizeof(void*)*1);
lean_inc(x_338);
lean_dec(x_9);
x_340 = l_Lake_readTraceFile_x3f(x_5, x_338, x_10);
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_340, 1);
lean_inc(x_342);
lean_dec(x_340);
x_343 = lean_ctor_get(x_341, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_341, 1);
lean_inc(x_344);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 x_345 = x_341;
} else {
 lean_dec_ref(x_341);
 x_345 = lean_box(0);
}
x_346 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_346, 0, x_344);
lean_ctor_set_uint8(x_346, sizeof(void*)*1, x_339);
if (lean_is_scalar(x_345)) {
 x_347 = lean_alloc_ctor(0, 2, 0);
} else {
 x_347 = x_345;
}
lean_ctor_set(x_347, 0, x_343);
lean_ctor_set(x_347, 1, x_346);
x_12 = x_347;
x_13 = x_342;
goto block_327;
}
block_327:
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_7);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_12, 1);
x_19 = lean_ctor_get(x_12, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
x_22 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__3(x_3, x_21, x_13);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = lean_unbox(x_24);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_free_object(x_22);
lean_free_object(x_12);
x_27 = lean_box(0);
x_28 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_buildFileUnlessUpToDate___spec__2___lambda__2(x_2, x_11, x_5, x_4, x_6, x_27, x_8, x_18, x_25);
return x_28;
}
else
{
uint8_t x_29; lean_object* x_30; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_29 = 1;
x_30 = lean_box(x_29);
lean_ctor_set(x_12, 0, x_30);
lean_ctor_set(x_22, 0, x_12);
return x_22;
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_22, 0);
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_22);
x_33 = lean_unbox(x_31);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_free_object(x_12);
x_34 = lean_box(0);
x_35 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_buildFileUnlessUpToDate___spec__2___lambda__2(x_2, x_11, x_5, x_4, x_6, x_34, x_8, x_18, x_32);
return x_35;
}
else
{
uint8_t x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_36 = 1;
x_37 = lean_box(x_36);
lean_ctor_set(x_12, 0, x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_12);
lean_ctor_set(x_38, 1, x_32);
return x_38;
}
}
}
else
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_39 = lean_ctor_get(x_18, 0);
x_40 = lean_ctor_get_uint8(x_18, sizeof(void*)*1);
lean_inc(x_39);
lean_dec(x_18);
x_41 = lean_ctor_get(x_4, 1);
lean_inc(x_41);
x_42 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__3(x_3, x_41, x_13);
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
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_40);
x_47 = lean_unbox(x_43);
lean_dec(x_43);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_45);
lean_free_object(x_12);
x_48 = lean_box(0);
x_49 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_buildFileUnlessUpToDate___spec__2___lambda__2(x_2, x_11, x_5, x_4, x_6, x_48, x_8, x_46, x_44);
return x_49;
}
else
{
uint8_t x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_50 = 1;
x_51 = lean_box(x_50);
lean_ctor_set(x_12, 1, x_46);
lean_ctor_set(x_12, 0, x_51);
if (lean_is_scalar(x_45)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_45;
}
lean_ctor_set(x_52, 0, x_12);
lean_ctor_set(x_52, 1, x_44);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_53 = lean_ctor_get(x_12, 1);
lean_inc(x_53);
lean_dec(x_12);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get_uint8(x_53, sizeof(void*)*1);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_56 = x_53;
} else {
 lean_dec_ref(x_53);
 x_56 = lean_box(0);
}
x_57 = lean_ctor_get(x_4, 1);
lean_inc(x_57);
x_58 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__3(x_3, x_57, x_13);
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
if (lean_is_scalar(x_56)) {
 x_62 = lean_alloc_ctor(0, 1, 1);
} else {
 x_62 = x_56;
}
lean_ctor_set(x_62, 0, x_54);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_55);
x_63 = lean_unbox(x_59);
lean_dec(x_59);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_61);
x_64 = lean_box(0);
x_65 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_buildFileUnlessUpToDate___spec__2___lambda__2(x_2, x_11, x_5, x_4, x_6, x_64, x_8, x_62, x_60);
return x_65;
}
else
{
uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_66 = 1;
x_67 = lean_box(x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_62);
if (lean_is_scalar(x_61)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_61;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_60);
return x_69;
}
}
}
else
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_12);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_ctor_get(x_12, 1);
x_72 = lean_ctor_get(x_12, 0);
lean_dec(x_72);
x_73 = !lean_is_exclusive(x_71);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__3(x_3, x_7, x_13);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = lean_ctor_get(x_74, 0);
x_77 = lean_ctor_get(x_74, 1);
x_78 = lean_unbox(x_76);
lean_dec(x_76);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_free_object(x_74);
lean_free_object(x_12);
x_79 = lean_box(0);
x_80 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_buildFileUnlessUpToDate___spec__2___lambda__2(x_2, x_11, x_5, x_4, x_6, x_79, x_8, x_71, x_77);
return x_80;
}
else
{
uint8_t x_81; lean_object* x_82; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_81 = 1;
x_82 = lean_box(x_81);
lean_ctor_set(x_12, 0, x_82);
lean_ctor_set(x_74, 0, x_12);
return x_74;
}
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = lean_ctor_get(x_74, 0);
x_84 = lean_ctor_get(x_74, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_74);
x_85 = lean_unbox(x_83);
lean_dec(x_83);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_free_object(x_12);
x_86 = lean_box(0);
x_87 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_buildFileUnlessUpToDate___spec__2___lambda__2(x_2, x_11, x_5, x_4, x_6, x_86, x_8, x_71, x_84);
return x_87;
}
else
{
uint8_t x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_88 = 1;
x_89 = lean_box(x_88);
lean_ctor_set(x_12, 0, x_89);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_12);
lean_ctor_set(x_90, 1, x_84);
return x_90;
}
}
}
else
{
lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_91 = lean_ctor_get(x_71, 0);
x_92 = lean_ctor_get_uint8(x_71, sizeof(void*)*1);
lean_inc(x_91);
lean_dec(x_71);
x_93 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__3(x_3, x_7, x_13);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_96 = x_93;
} else {
 lean_dec_ref(x_93);
 x_96 = lean_box(0);
}
x_97 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_97, 0, x_91);
lean_ctor_set_uint8(x_97, sizeof(void*)*1, x_92);
x_98 = lean_unbox(x_94);
lean_dec(x_94);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_96);
lean_free_object(x_12);
x_99 = lean_box(0);
x_100 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_buildFileUnlessUpToDate___spec__2___lambda__2(x_2, x_11, x_5, x_4, x_6, x_99, x_8, x_97, x_95);
return x_100;
}
else
{
uint8_t x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_101 = 1;
x_102 = lean_box(x_101);
lean_ctor_set(x_12, 1, x_97);
lean_ctor_set(x_12, 0, x_102);
if (lean_is_scalar(x_96)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_96;
}
lean_ctor_set(x_103, 0, x_12);
lean_ctor_set(x_103, 1, x_95);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_104 = lean_ctor_get(x_12, 1);
lean_inc(x_104);
lean_dec(x_12);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get_uint8(x_104, sizeof(void*)*1);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 x_107 = x_104;
} else {
 lean_dec_ref(x_104);
 x_107 = lean_box(0);
}
x_108 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__3(x_3, x_7, x_13);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_111 = x_108;
} else {
 lean_dec_ref(x_108);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_112 = lean_alloc_ctor(0, 1, 1);
} else {
 x_112 = x_107;
}
lean_ctor_set(x_112, 0, x_105);
lean_ctor_set_uint8(x_112, sizeof(void*)*1, x_106);
x_113 = lean_unbox(x_109);
lean_dec(x_109);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_111);
x_114 = lean_box(0);
x_115 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_buildFileUnlessUpToDate___spec__2___lambda__2(x_2, x_11, x_5, x_4, x_6, x_114, x_8, x_112, x_110);
return x_115;
}
else
{
uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_116 = 1;
x_117 = lean_box(x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_112);
if (lean_is_scalar(x_111)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_111;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_110);
return x_119;
}
}
}
}
else
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_14);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_121 = lean_ctor_get(x_14, 0);
x_122 = lean_ctor_get(x_12, 1);
lean_inc(x_122);
lean_dec(x_12);
x_123 = lean_ctor_get(x_121, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
lean_dec(x_121);
lean_ctor_set(x_14, 0, x_123);
lean_inc(x_4);
x_125 = l_Lake_checkHashUpToDate___at_Lake_buildFileUnlessUpToDate___spec__4(x_3, x_4, x_14, x_7, x_8, x_122, x_13);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_128 = x_125;
} else {
 lean_dec_ref(x_125);
 x_128 = lean_box(0);
}
x_129 = !lean_is_exclusive(x_126);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_196; 
x_130 = lean_ctor_get(x_126, 0);
x_131 = lean_ctor_get(x_126, 1);
x_196 = lean_unbox(x_130);
lean_dec(x_130);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; 
lean_free_object(x_126);
lean_dec(x_128);
lean_dec(x_124);
x_197 = lean_box(0);
x_198 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_buildFileUnlessUpToDate___spec__2___lambda__2(x_2, x_11, x_5, x_4, x_6, x_197, x_8, x_131, x_127);
return x_198;
}
else
{
uint8_t x_199; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_199 = !lean_is_exclusive(x_131);
if (x_199 == 0)
{
uint8_t x_200; lean_object* x_201; uint8_t x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_200 = lean_ctor_get_uint8(x_131, sizeof(void*)*1);
x_201 = l_Lake_instOrdJobAction;
x_202 = 1;
x_203 = lean_box(x_200);
x_204 = lean_box(x_202);
x_205 = l_instDecidableRelLe___rarg(x_201, x_203, x_204);
if (x_205 == 0)
{
lean_object* x_206; 
x_206 = lean_box(0);
lean_ctor_set(x_126, 0, x_206);
x_132 = x_126;
x_133 = x_127;
goto block_195;
}
else
{
lean_object* x_207; 
lean_ctor_set_uint8(x_131, sizeof(void*)*1, x_202);
x_207 = lean_box(0);
lean_ctor_set(x_126, 0, x_207);
x_132 = x_126;
x_133 = x_127;
goto block_195;
}
}
else
{
lean_object* x_208; uint8_t x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; 
x_208 = lean_ctor_get(x_131, 0);
x_209 = lean_ctor_get_uint8(x_131, sizeof(void*)*1);
lean_inc(x_208);
lean_dec(x_131);
x_210 = l_Lake_instOrdJobAction;
x_211 = 1;
x_212 = lean_box(x_209);
x_213 = lean_box(x_211);
x_214 = l_instDecidableRelLe___rarg(x_210, x_212, x_213);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_215, 0, x_208);
lean_ctor_set_uint8(x_215, sizeof(void*)*1, x_209);
x_216 = lean_box(0);
lean_ctor_set(x_126, 1, x_215);
lean_ctor_set(x_126, 0, x_216);
x_132 = x_126;
x_133 = x_127;
goto block_195;
}
else
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_217, 0, x_208);
lean_ctor_set_uint8(x_217, sizeof(void*)*1, x_211);
x_218 = lean_box(0);
lean_ctor_set(x_126, 1, x_217);
lean_ctor_set(x_126, 0, x_218);
x_132 = x_126;
x_133 = x_127;
goto block_195;
}
}
}
block_195:
{
uint8_t x_134; 
x_134 = !lean_is_exclusive(x_132);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_135 = lean_ctor_get(x_132, 1);
x_136 = lean_ctor_get(x_132, 0);
lean_dec(x_136);
x_137 = lean_array_get_size(x_124);
x_138 = lean_unsigned_to_nat(0u);
x_139 = lean_nat_dec_lt(x_138, x_137);
if (x_139 == 0)
{
uint8_t x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_137);
lean_dec(x_124);
lean_dec(x_8);
x_140 = 1;
x_141 = lean_box(x_140);
lean_ctor_set(x_132, 0, x_141);
if (lean_is_scalar(x_128)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_128;
}
lean_ctor_set(x_142, 0, x_132);
lean_ctor_set(x_142, 1, x_133);
return x_142;
}
else
{
uint8_t x_143; 
x_143 = lean_nat_dec_le(x_137, x_137);
if (x_143 == 0)
{
uint8_t x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_137);
lean_dec(x_124);
lean_dec(x_8);
x_144 = 1;
x_145 = lean_box(x_144);
lean_ctor_set(x_132, 0, x_145);
if (lean_is_scalar(x_128)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_128;
}
lean_ctor_set(x_146, 0, x_132);
lean_ctor_set(x_146, 1, x_133);
return x_146;
}
else
{
size_t x_147; size_t x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
lean_free_object(x_132);
lean_dec(x_128);
x_147 = 0;
x_148 = lean_usize_of_nat(x_137);
lean_dec(x_137);
x_149 = lean_box(0);
x_150 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate___spec__6(x_124, x_147, x_148, x_149, x_8, x_135, x_133);
lean_dec(x_8);
lean_dec(x_124);
x_151 = !lean_is_exclusive(x_150);
if (x_151 == 0)
{
lean_object* x_152; uint8_t x_153; 
x_152 = lean_ctor_get(x_150, 0);
x_153 = !lean_is_exclusive(x_152);
if (x_153 == 0)
{
lean_object* x_154; uint8_t x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_152, 0);
lean_dec(x_154);
x_155 = 1;
x_156 = lean_box(x_155);
lean_ctor_set(x_152, 0, x_156);
return x_150;
}
else
{
lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; 
x_157 = lean_ctor_get(x_152, 1);
lean_inc(x_157);
lean_dec(x_152);
x_158 = 1;
x_159 = lean_box(x_158);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_157);
lean_ctor_set(x_150, 0, x_160);
return x_150;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_161 = lean_ctor_get(x_150, 0);
x_162 = lean_ctor_get(x_150, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_150);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_164 = x_161;
} else {
 lean_dec_ref(x_161);
 x_164 = lean_box(0);
}
x_165 = 1;
x_166 = lean_box(x_165);
if (lean_is_scalar(x_164)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_164;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_163);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_162);
return x_168;
}
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_169 = lean_ctor_get(x_132, 1);
lean_inc(x_169);
lean_dec(x_132);
x_170 = lean_array_get_size(x_124);
x_171 = lean_unsigned_to_nat(0u);
x_172 = lean_nat_dec_lt(x_171, x_170);
if (x_172 == 0)
{
uint8_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_170);
lean_dec(x_124);
lean_dec(x_8);
x_173 = 1;
x_174 = lean_box(x_173);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_169);
if (lean_is_scalar(x_128)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_128;
}
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_133);
return x_176;
}
else
{
uint8_t x_177; 
x_177 = lean_nat_dec_le(x_170, x_170);
if (x_177 == 0)
{
uint8_t x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_170);
lean_dec(x_124);
lean_dec(x_8);
x_178 = 1;
x_179 = lean_box(x_178);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_169);
if (lean_is_scalar(x_128)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_128;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_133);
return x_181;
}
else
{
size_t x_182; size_t x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_128);
x_182 = 0;
x_183 = lean_usize_of_nat(x_170);
lean_dec(x_170);
x_184 = lean_box(0);
x_185 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate___spec__6(x_124, x_182, x_183, x_184, x_8, x_169, x_133);
lean_dec(x_8);
lean_dec(x_124);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_188 = x_185;
} else {
 lean_dec_ref(x_185);
 x_188 = lean_box(0);
}
x_189 = lean_ctor_get(x_186, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_190 = x_186;
} else {
 lean_dec_ref(x_186);
 x_190 = lean_box(0);
}
x_191 = 1;
x_192 = lean_box(x_191);
if (lean_is_scalar(x_190)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_190;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_189);
if (lean_is_scalar(x_188)) {
 x_194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_194 = x_188;
}
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_187);
return x_194;
}
}
}
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_251; 
x_219 = lean_ctor_get(x_126, 0);
x_220 = lean_ctor_get(x_126, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_126);
x_251 = lean_unbox(x_219);
lean_dec(x_219);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; 
lean_dec(x_128);
lean_dec(x_124);
x_252 = lean_box(0);
x_253 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_buildFileUnlessUpToDate___spec__2___lambda__2(x_2, x_11, x_5, x_4, x_6, x_252, x_8, x_220, x_127);
return x_253;
}
else
{
lean_object* x_254; uint8_t x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_254 = lean_ctor_get(x_220, 0);
lean_inc(x_254);
x_255 = lean_ctor_get_uint8(x_220, sizeof(void*)*1);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 x_256 = x_220;
} else {
 lean_dec_ref(x_220);
 x_256 = lean_box(0);
}
x_257 = l_Lake_instOrdJobAction;
x_258 = 1;
x_259 = lean_box(x_255);
x_260 = lean_box(x_258);
x_261 = l_instDecidableRelLe___rarg(x_257, x_259, x_260);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
if (lean_is_scalar(x_256)) {
 x_262 = lean_alloc_ctor(0, 1, 1);
} else {
 x_262 = x_256;
}
lean_ctor_set(x_262, 0, x_254);
lean_ctor_set_uint8(x_262, sizeof(void*)*1, x_255);
x_263 = lean_box(0);
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_262);
x_221 = x_264;
x_222 = x_127;
goto block_250;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
if (lean_is_scalar(x_256)) {
 x_265 = lean_alloc_ctor(0, 1, 1);
} else {
 x_265 = x_256;
}
lean_ctor_set(x_265, 0, x_254);
lean_ctor_set_uint8(x_265, sizeof(void*)*1, x_258);
x_266 = lean_box(0);
x_267 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_265);
x_221 = x_267;
x_222 = x_127;
goto block_250;
}
}
block_250:
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; 
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
x_225 = lean_array_get_size(x_124);
x_226 = lean_unsigned_to_nat(0u);
x_227 = lean_nat_dec_lt(x_226, x_225);
if (x_227 == 0)
{
uint8_t x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_225);
lean_dec(x_124);
lean_dec(x_8);
x_228 = 1;
x_229 = lean_box(x_228);
if (lean_is_scalar(x_224)) {
 x_230 = lean_alloc_ctor(0, 2, 0);
} else {
 x_230 = x_224;
}
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_223);
if (lean_is_scalar(x_128)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_128;
}
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_222);
return x_231;
}
else
{
uint8_t x_232; 
x_232 = lean_nat_dec_le(x_225, x_225);
if (x_232 == 0)
{
uint8_t x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_225);
lean_dec(x_124);
lean_dec(x_8);
x_233 = 1;
x_234 = lean_box(x_233);
if (lean_is_scalar(x_224)) {
 x_235 = lean_alloc_ctor(0, 2, 0);
} else {
 x_235 = x_224;
}
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_223);
if (lean_is_scalar(x_128)) {
 x_236 = lean_alloc_ctor(0, 2, 0);
} else {
 x_236 = x_128;
}
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_222);
return x_236;
}
else
{
size_t x_237; size_t x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_224);
lean_dec(x_128);
x_237 = 0;
x_238 = lean_usize_of_nat(x_225);
lean_dec(x_225);
x_239 = lean_box(0);
x_240 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate___spec__6(x_124, x_237, x_238, x_239, x_8, x_223, x_222);
lean_dec(x_8);
lean_dec(x_124);
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_243 = x_240;
} else {
 lean_dec_ref(x_240);
 x_243 = lean_box(0);
}
x_244 = lean_ctor_get(x_241, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_245 = x_241;
} else {
 lean_dec_ref(x_241);
 x_245 = lean_box(0);
}
x_246 = 1;
x_247 = lean_box(x_246);
if (lean_is_scalar(x_245)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_245;
}
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_244);
if (lean_is_scalar(x_243)) {
 x_249 = lean_alloc_ctor(0, 2, 0);
} else {
 x_249 = x_243;
}
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_242);
return x_249;
}
}
}
}
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_310; 
x_268 = lean_ctor_get(x_14, 0);
lean_inc(x_268);
lean_dec(x_14);
x_269 = lean_ctor_get(x_12, 1);
lean_inc(x_269);
lean_dec(x_12);
x_270 = lean_ctor_get(x_268, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_268, 1);
lean_inc(x_271);
lean_dec(x_268);
x_272 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_272, 0, x_270);
lean_inc(x_4);
x_273 = l_Lake_checkHashUpToDate___at_Lake_buildFileUnlessUpToDate___spec__4(x_3, x_4, x_272, x_7, x_8, x_269, x_13);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 x_276 = x_273;
} else {
 lean_dec_ref(x_273);
 x_276 = lean_box(0);
}
x_277 = lean_ctor_get(x_274, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_274, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_279 = x_274;
} else {
 lean_dec_ref(x_274);
 x_279 = lean_box(0);
}
x_310 = lean_unbox(x_277);
lean_dec(x_277);
if (x_310 == 0)
{
lean_object* x_311; lean_object* x_312; 
lean_dec(x_279);
lean_dec(x_276);
lean_dec(x_271);
x_311 = lean_box(0);
x_312 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_buildFileUnlessUpToDate___spec__2___lambda__2(x_2, x_11, x_5, x_4, x_6, x_311, x_8, x_278, x_275);
return x_312;
}
else
{
lean_object* x_313; uint8_t x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_313 = lean_ctor_get(x_278, 0);
lean_inc(x_313);
x_314 = lean_ctor_get_uint8(x_278, sizeof(void*)*1);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 x_315 = x_278;
} else {
 lean_dec_ref(x_278);
 x_315 = lean_box(0);
}
x_316 = l_Lake_instOrdJobAction;
x_317 = 1;
x_318 = lean_box(x_314);
x_319 = lean_box(x_317);
x_320 = l_instDecidableRelLe___rarg(x_316, x_318, x_319);
if (x_320 == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
if (lean_is_scalar(x_315)) {
 x_321 = lean_alloc_ctor(0, 1, 1);
} else {
 x_321 = x_315;
}
lean_ctor_set(x_321, 0, x_313);
lean_ctor_set_uint8(x_321, sizeof(void*)*1, x_314);
x_322 = lean_box(0);
if (lean_is_scalar(x_279)) {
 x_323 = lean_alloc_ctor(0, 2, 0);
} else {
 x_323 = x_279;
}
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_321);
x_280 = x_323;
x_281 = x_275;
goto block_309;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
if (lean_is_scalar(x_315)) {
 x_324 = lean_alloc_ctor(0, 1, 1);
} else {
 x_324 = x_315;
}
lean_ctor_set(x_324, 0, x_313);
lean_ctor_set_uint8(x_324, sizeof(void*)*1, x_317);
x_325 = lean_box(0);
if (lean_is_scalar(x_279)) {
 x_326 = lean_alloc_ctor(0, 2, 0);
} else {
 x_326 = x_279;
}
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_324);
x_280 = x_326;
x_281 = x_275;
goto block_309;
}
}
block_309:
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; 
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
x_284 = lean_array_get_size(x_271);
x_285 = lean_unsigned_to_nat(0u);
x_286 = lean_nat_dec_lt(x_285, x_284);
if (x_286 == 0)
{
uint8_t x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
lean_dec(x_284);
lean_dec(x_271);
lean_dec(x_8);
x_287 = 1;
x_288 = lean_box(x_287);
if (lean_is_scalar(x_283)) {
 x_289 = lean_alloc_ctor(0, 2, 0);
} else {
 x_289 = x_283;
}
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_282);
if (lean_is_scalar(x_276)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_276;
}
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_281);
return x_290;
}
else
{
uint8_t x_291; 
x_291 = lean_nat_dec_le(x_284, x_284);
if (x_291 == 0)
{
uint8_t x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_dec(x_284);
lean_dec(x_271);
lean_dec(x_8);
x_292 = 1;
x_293 = lean_box(x_292);
if (lean_is_scalar(x_283)) {
 x_294 = lean_alloc_ctor(0, 2, 0);
} else {
 x_294 = x_283;
}
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_282);
if (lean_is_scalar(x_276)) {
 x_295 = lean_alloc_ctor(0, 2, 0);
} else {
 x_295 = x_276;
}
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_281);
return x_295;
}
else
{
size_t x_296; size_t x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
lean_dec(x_283);
lean_dec(x_276);
x_296 = 0;
x_297 = lean_usize_of_nat(x_284);
lean_dec(x_284);
x_298 = lean_box(0);
x_299 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate___spec__6(x_271, x_296, x_297, x_298, x_8, x_282, x_281);
lean_dec(x_8);
lean_dec(x_271);
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
x_303 = lean_ctor_get(x_300, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 lean_ctor_release(x_300, 1);
 x_304 = x_300;
} else {
 lean_dec_ref(x_300);
 x_304 = lean_box(0);
}
x_305 = 1;
x_306 = lean_box(x_305);
if (lean_is_scalar(x_304)) {
 x_307 = lean_alloc_ctor(0, 2, 0);
} else {
 x_307 = x_304;
}
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_303);
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
}
}
}
}
}
static lean_object* _init_l_Lake_buildFileUnlessUpToDate___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(".trace", 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_7 = l_Lake_buildFileUnlessUpToDate___closed__1;
lean_inc(x_1);
x_8 = lean_string_append(x_1, x_7);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
x_10 = 3;
lean_inc(x_4);
lean_inc(x_1);
x_11 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_buildFileUnlessUpToDate___spec__2(x_1, x_3, x_1, x_2, x_8, x_10, x_9, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lake_fetchFileTrace(x_1, x_4, x_14, x_13);
lean_dec(x_4);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_4);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_11, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_11, 0, x_21);
return x_11;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_dec(x_11);
x_23 = lean_ctor_get(x_12, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_25 = x_12;
} else {
 lean_dec_ref(x_12);
 x_25 = lean_box(0);
}
if (lean_is_scalar(x_25)) {
 x_26 = lean_alloc_ctor(1, 2, 0);
} else {
 x_26 = x_25;
}
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_4);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_11);
if (x_28 == 0)
{
return x_11;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_11, 0);
x_30 = lean_ctor_get(x_11, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_11);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__3(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lake_buildFileUnlessUpToDate___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lake_buildFileUnlessUpToDate___spec__5(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___at_Lake_buildFileUnlessUpToDate___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_checkHashUpToDate___at_Lake_buildFileUnlessUpToDate___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate___spec__6(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_buildFileUnlessUpToDate___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_buildFileUnlessUpToDate___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_buildFileUnlessUpToDate___spec__2___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_buildFileUnlessUpToDate___spec__2___lambda__2(x_1, x_2, x_3, x_4, x_10, x_6, x_7, x_8, x_9);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_buildFileUnlessUpToDate___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_6);
lean_dec(x_6);
x_12 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_buildFileUnlessUpToDate___spec__2(x_1, x_2, x_3, x_4, x_5, x_11, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_buildFileAfterDep___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_buildFileAfterDep___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_buildFileAfterDep___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__1() {
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
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init.Data.String.Extra", 22);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("String.fromUTF8!", 16);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid UTF-8 string", 20);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__2;
x_2 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__3;
x_3 = lean_unsigned_to_nat(92u);
x_4 = lean_unsigned_to_nat(47u);
x_5 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__1;
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
x_17 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_buildFileAfterDep___spec__2), 5, 2);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_1);
x_18 = l_IO_withStdin___at_Lake_buildFileAfterDep___spec__3(x_15, x_17, x_3, x_4, x_14);
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
x_32 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__5;
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
x_35 = lean_string_from_utf8_unchecked(x_30);
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
x_41 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__5;
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
x_45 = lean_string_from_utf8_unchecked(x_39);
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
x_61 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__5;
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
x_65 = lean_string_from_utf8_unchecked(x_59);
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
x_83 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__5;
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
x_88 = lean_string_from_utf8_unchecked(x_81);
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
x_112 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lake_buildFileAfterDep___spec__4), 5, 2);
lean_closure_set(x_112, 0, x_16);
lean_closure_set(x_112, 1, x_1);
x_113 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_buildFileAfterDep___spec__2), 5, 2);
lean_closure_set(x_113, 0, x_16);
lean_closure_set(x_113, 1, x_112);
x_114 = l_IO_withStdin___at_Lake_buildFileAfterDep___spec__3(x_15, x_113, x_3, x_4, x_14);
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
x_128 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__5;
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
x_131 = lean_string_from_utf8_unchecked(x_126);
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
x_137 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__5;
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
x_141 = lean_string_from_utf8_unchecked(x_135);
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
x_157 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__5;
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
x_161 = lean_string_from_utf8_unchecked(x_155);
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
x_179 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__5;
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
x_184 = lean_string_from_utf8_unchecked(x_177);
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
x_218 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__1;
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
x_228 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_buildFileAfterDep___spec__2), 5, 2);
lean_closure_set(x_228, 0, x_227);
lean_closure_set(x_228, 1, x_1);
x_229 = l_IO_withStdin___at_Lake_buildFileAfterDep___spec__3(x_226, x_228, x_3, x_225, x_224);
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
x_245 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__5;
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
x_250 = lean_string_from_utf8_unchecked(x_243);
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
x_269 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lake_buildFileAfterDep___spec__4), 5, 2);
lean_closure_set(x_269, 0, x_227);
lean_closure_set(x_269, 1, x_1);
x_270 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_buildFileAfterDep___spec__2), 5, 2);
lean_closure_set(x_270, 0, x_227);
lean_closure_set(x_270, 1, x_269);
x_271 = l_IO_withStdin___at_Lake_buildFileAfterDep___spec__3(x_226, x_270, x_3, x_225, x_224);
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
x_287 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__5;
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
x_292 = lean_string_from_utf8_unchecked(x_285);
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
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lake_BuildTrace_mix(x_1, x_5);
x_10 = lean_apply_1(x_2, x_3);
lean_inc(x_4);
x_11 = l_Lake_buildFileUnlessUpToDate(x_4, x_9, x_10, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_12, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_11, 0, x_21);
return x_11;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_dec(x_11);
x_23 = lean_ctor_get(x_12, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_25 = x_12;
} else {
 lean_dec_ref(x_12);
 x_25 = lean_box(0);
}
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_23);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_22);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_11);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_11, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_12);
if (x_31 == 0)
{
return x_11;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_12, 0);
x_33 = lean_ctor_get(x_12, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_12);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_11, 0, x_34);
return x_11;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_11, 1);
lean_inc(x_35);
lean_dec(x_11);
x_36 = lean_ctor_get(x_12, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_12, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_38 = x_12;
} else {
 lean_dec_ref(x_12);
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
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_11);
if (x_41 == 0)
{
return x_11;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_11, 0);
x_43 = lean_ctor_get(x_11, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_11);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
static lean_object* _init_l_Lake_buildFileAfterDep___rarg___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("stdout/stderr:\n", 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___rarg___lambda__1), 8, 4);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_9);
lean_closure_set(x_11, 3, x_2);
x_12 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_12, 0, x_3);
lean_closure_set(x_12, 1, x_11);
x_13 = 1;
lean_inc(x_4);
x_14 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1(x_12, x_13, x_4, x_8, x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = l_String_isEmpty(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; 
x_22 = l_Lake_buildFileAfterDep___rarg___lambda__3___closed__1;
x_23 = lean_string_append(x_22, x_19);
lean_dec(x_19);
x_24 = l_Lake_readTraceFile_x3f___closed__1;
x_25 = lean_string_append(x_23, x_24);
x_26 = 1;
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_array_push(x_29, x_27);
lean_ctor_set(x_18, 0, x_30);
x_31 = lean_box(0);
x_32 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_20, x_31, x_4, x_18, x_17);
lean_dec(x_4);
return x_32;
}
else
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_18, 0);
x_34 = lean_ctor_get_uint8(x_18, sizeof(void*)*1);
lean_inc(x_33);
lean_dec(x_18);
x_35 = lean_array_push(x_33, x_27);
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_34);
x_37 = lean_box(0);
x_38 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_20, x_37, x_4, x_36, x_17);
lean_dec(x_4);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_19);
x_39 = lean_box(0);
x_40 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_20, x_39, x_4, x_18, x_17);
lean_dec(x_4);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_14);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_14, 0);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_15);
if (x_43 == 0)
{
return x_14;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_15, 0);
x_45 = lean_ctor_get(x_15, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_15);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_14, 0, x_46);
return x_14;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_14, 1);
lean_inc(x_47);
lean_dec(x_14);
x_48 = lean_ctor_get(x_15, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_15, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_50 = x_15;
} else {
 lean_dec_ref(x_15);
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
else
{
uint8_t x_53; 
lean_dec(x_4);
x_53 = !lean_is_exclusive(x_14);
if (x_53 == 0)
{
return x_14;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_14, 0);
x_55 = lean_ctor_get(x_14, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_14);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_5);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_5);
lean_ctor_set(x_58, 1, x_6);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_5, 0);
x_60 = lean_ctor_get(x_5, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_5);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_6);
return x_62;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___rarg___lambda__3), 6, 4);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_4);
lean_closure_set(x_10, 3, x_5);
x_11 = l_Task_Priority_default;
x_12 = 0;
x_13 = lean_io_map_task(x_10, x_8, x_11, x_12, x_6);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_ctor_set(x_2, 0, x_15);
lean_ctor_set(x_13, 0, x_2);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_13);
lean_ctor_set(x_2, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_free_object(x_2);
lean_dec(x_9);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_2);
x_25 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___rarg___lambda__3), 6, 4);
lean_closure_set(x_25, 0, x_3);
lean_closure_set(x_25, 1, x_1);
lean_closure_set(x_25, 2, x_4);
lean_closure_set(x_25, 3, x_5);
x_26 = l_Task_Priority_default;
x_27 = 0;
x_28 = lean_io_map_task(x_25, x_23, x_26, x_27, x_6);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
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
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_24);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_24);
x_34 = lean_ctor_get(x_28, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_36 = x_28;
} else {
 lean_dec_ref(x_28);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepList___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___rarg___lambda__1), 8, 4);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_9);
lean_closure_set(x_11, 3, x_2);
x_12 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_12, 0, x_3);
lean_closure_set(x_12, 1, x_11);
x_13 = 1;
lean_inc(x_4);
x_14 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1(x_12, x_13, x_4, x_8, x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = l_String_isEmpty(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; 
x_22 = l_Lake_buildFileAfterDep___rarg___lambda__3___closed__1;
x_23 = lean_string_append(x_22, x_19);
lean_dec(x_19);
x_24 = l_Lake_readTraceFile_x3f___closed__1;
x_25 = lean_string_append(x_23, x_24);
x_26 = 1;
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_array_push(x_29, x_27);
lean_ctor_set(x_18, 0, x_30);
x_31 = lean_box(0);
x_32 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_20, x_31, x_4, x_18, x_17);
lean_dec(x_4);
return x_32;
}
else
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_18, 0);
x_34 = lean_ctor_get_uint8(x_18, sizeof(void*)*1);
lean_inc(x_33);
lean_dec(x_18);
x_35 = lean_array_push(x_33, x_27);
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_34);
x_37 = lean_box(0);
x_38 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_20, x_37, x_4, x_36, x_17);
lean_dec(x_4);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_19);
x_39 = lean_box(0);
x_40 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_20, x_39, x_4, x_18, x_17);
lean_dec(x_4);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_14);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_14, 0);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_15);
if (x_43 == 0)
{
return x_14;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_15, 0);
x_45 = lean_ctor_get(x_15, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_15);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_14, 0, x_46);
return x_14;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_14, 1);
lean_inc(x_47);
lean_dec(x_14);
x_48 = lean_ctor_get(x_15, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_15, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_50 = x_15;
} else {
 lean_dec_ref(x_15);
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
else
{
uint8_t x_53; 
lean_dec(x_4);
x_53 = !lean_is_exclusive(x_14);
if (x_53 == 0)
{
return x_14;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_14, 0);
x_55 = lean_ctor_get(x_14, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_14);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_5);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_5);
lean_ctor_set(x_58, 1, x_6);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_5, 0);
x_60 = lean_ctor_get(x_5, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_5);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_6);
return x_62;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepList___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lake_BuildJob_collectList___rarg(x_2);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDepList___rarg___lambda__1), 6, 4);
lean_closure_set(x_11, 0, x_3);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_4);
lean_closure_set(x_11, 3, x_5);
x_12 = l_Task_Priority_default;
x_13 = 0;
x_14 = lean_io_map_task(x_11, x_9, x_12, x_13, x_6);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_ctor_set(x_7, 0, x_16);
lean_ctor_set(x_14, 0, x_7);
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
lean_ctor_set(x_7, 0, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_free_object(x_7);
lean_dec(x_10);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_7);
x_26 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDepList___rarg___lambda__1), 6, 4);
lean_closure_set(x_26, 0, x_3);
lean_closure_set(x_26, 1, x_1);
lean_closure_set(x_26, 2, x_4);
lean_closure_set(x_26, 3, x_5);
x_27 = l_Task_Priority_default;
x_28 = 0;
x_29 = lean_io_map_task(x_26, x_24, x_27, x_28, x_6);
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
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_25);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_25);
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
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDepList___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepArray___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lake_BuildJob_collectArray___rarg(x_2);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDepList___rarg___lambda__1), 6, 4);
lean_closure_set(x_11, 0, x_3);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_4);
lean_closure_set(x_11, 3, x_5);
x_12 = l_Task_Priority_default;
x_13 = 0;
x_14 = lean_io_map_task(x_11, x_9, x_12, x_13, x_6);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_ctor_set(x_7, 0, x_16);
lean_ctor_set(x_14, 0, x_7);
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
lean_ctor_set(x_7, 0, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_free_object(x_7);
lean_dec(x_10);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_7);
x_26 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDepList___rarg___lambda__1), 6, 4);
lean_closure_set(x_26, 0, x_3);
lean_closure_set(x_26, 1, x_1);
lean_closure_set(x_26, 2, x_4);
lean_closure_set(x_26, 3, x_5);
x_27 = l_Task_Priority_default;
x_28 = 0;
x_29 = lean_io_map_task(x_26, x_24, x_27, x_28, x_6);
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
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_25);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_25);
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
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDepArray___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepArray___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_buildFileAfterDepArray___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at_Lake_inputBinFile___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_computeFileHash(x_1, x_2);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_4);
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
return x_6;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
return x_3;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = l_Lake_BuildTrace_compute___at_Lake_inputBinFile___spec__1(x_1, x_4);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_7, 0);
x_19 = lean_io_error_to_string(x_18);
x_20 = 3;
x_21 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
x_22 = lean_array_get_size(x_6);
x_23 = lean_array_push(x_6, x_21);
lean_ctor_set(x_3, 0, x_23);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_24);
return x_7;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_7, 0);
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_7);
x_27 = lean_io_error_to_string(x_25);
x_28 = 3;
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
x_30 = lean_array_get_size(x_6);
x_31 = lean_array_push(x_6, x_29);
lean_ctor_set(x_3, 0, x_31);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_3);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_26);
return x_33;
}
}
}
else
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_3, 0);
x_35 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
lean_inc(x_34);
lean_dec(x_3);
x_36 = l_Lake_BuildTrace_compute___at_Lake_inputBinFile___spec__1(x_1, x_4);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
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
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_35);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_37);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
if (lean_is_scalar(x_39)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_39;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_38);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_1);
x_44 = lean_ctor_get(x_36, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_46 = x_36;
} else {
 lean_dec_ref(x_36);
 x_46 = lean_box(0);
}
x_47 = lean_io_error_to_string(x_44);
x_48 = 3;
x_49 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_48);
x_50 = lean_array_get_size(x_34);
x_51 = lean_array_push(x_34, x_49);
x_52 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_35);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
if (lean_is_scalar(x_46)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_46;
 lean_ctor_set_tag(x_54, 0);
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_45);
return x_54;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 1;
lean_inc(x_2);
x_6 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1(x_1, x_5, x_2, x_3, x_4);
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
x_14 = l_Lake_buildFileAfterDep___rarg___lambda__3___closed__1;
x_15 = lean_string_append(x_14, x_11);
lean_dec(x_11);
x_16 = l_Lake_readTraceFile_x3f___closed__1;
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
x_24 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_12, x_23, x_2, x_10, x_9);
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
x_30 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_12, x_29, x_2, x_28, x_9);
lean_dec(x_2);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_11);
x_31 = lean_box(0);
x_32 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_12, x_31, x_2, x_10, x_9);
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
static lean_object* _init_l_Lake_inputBinFile___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__3;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_alloc_closure((void*)(l_Lake_inputBinFile___lambda__1___boxed), 4, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lake_inputBinFile___closed__1;
x_6 = lean_alloc_closure((void*)(l_Lake_inputBinFile___lambda__2), 4, 3);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_5);
x_7 = l_Task_Priority_default;
x_8 = lean_io_as_task(x_6, x_7, x_3);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lake_readTraceFile_x3f___closed__1;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = l_Lake_readTraceFile_x3f___closed__1;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
return x_8;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_8, 0);
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at_Lake_inputBinFile___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_BuildTrace_compute___at_Lake_inputBinFile___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_inputBinFile___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_inputBinFile___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at_Lake_inputTextFile___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_4);
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
return x_6;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
return x_3;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = l_Lake_BuildTrace_compute___at_Lake_inputTextFile___spec__1(x_1, x_4);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_7, 0);
x_19 = lean_io_error_to_string(x_18);
x_20 = 3;
x_21 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
x_22 = lean_array_get_size(x_6);
x_23 = lean_array_push(x_6, x_21);
lean_ctor_set(x_3, 0, x_23);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_24);
return x_7;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_7, 0);
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_7);
x_27 = lean_io_error_to_string(x_25);
x_28 = 3;
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
x_30 = lean_array_get_size(x_6);
x_31 = lean_array_push(x_6, x_29);
lean_ctor_set(x_3, 0, x_31);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_3);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_26);
return x_33;
}
}
}
else
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_3, 0);
x_35 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
lean_inc(x_34);
lean_dec(x_3);
x_36 = l_Lake_BuildTrace_compute___at_Lake_inputTextFile___spec__1(x_1, x_4);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
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
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_35);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_37);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
if (lean_is_scalar(x_39)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_39;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_38);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_1);
x_44 = lean_ctor_get(x_36, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_46 = x_36;
} else {
 lean_dec_ref(x_36);
 x_46 = lean_box(0);
}
x_47 = lean_io_error_to_string(x_44);
x_48 = 3;
x_49 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_48);
x_50 = lean_array_get_size(x_34);
x_51 = lean_array_push(x_34, x_49);
x_52 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_35);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
if (lean_is_scalar(x_46)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_46;
 lean_ctor_set_tag(x_54, 0);
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_45);
return x_54;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_alloc_closure((void*)(l_Lake_inputTextFile___lambda__1___boxed), 4, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lake_inputBinFile___closed__1;
x_6 = lean_alloc_closure((void*)(l_Lake_inputBinFile___lambda__2), 4, 3);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_5);
x_7 = l_Task_Priority_default;
x_8 = lean_io_as_task(x_6, x_7, x_3);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lake_readTraceFile_x3f___closed__1;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = l_Lake_readTraceFile_x3f___closed__1;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
return x_8;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_8, 0);
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at_Lake_inputTextFile___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_BuildTrace_compute___at_Lake_inputTextFile___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_inputTextFile___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_inputTextFile___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_inputBinFile(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_Array_foldlMUnsafe_fold___at_Lake_buildO___spec__2(lean_object* x_1, size_t x_2, size_t x_3, uint64_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; size_t x_11; size_t x_12; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_string_hash(x_6);
lean_dec(x_6);
x_8 = 1723;
x_9 = lean_uint64_mix_hash(x_8, x_7);
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
LEAN_EXPORT uint64_t l_Lake_computeArrayHash___at_Lake_buildO___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
if (x_4 == 0)
{
uint64_t x_5; 
lean_dec(x_2);
x_5 = l_Lake_Hash_nil;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_2, x_2);
if (x_6 == 0)
{
uint64_t x_7; 
lean_dec(x_2);
x_7 = l_Lake_Hash_nil;
return x_7;
}
else
{
size_t x_8; size_t x_9; uint64_t x_10; uint64_t x_11; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_10 = l_Lake_Hash_nil;
x_11 = l_Array_foldlMUnsafe_fold___at_Lake_buildO___spec__2(x_1, x_8, x_9, x_10);
return x_11;
}
}
}
}
static lean_object* _init_l_Lake_buildO___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_buildO___lambda__1___closed__2() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lake_buildO___lambda__1___closed__1;
x_3 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint64_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = l_Lake_computeArrayHash___at_Lake_buildO___spec__1(x_1);
x_7 = l_Lake_platformTrace;
x_8 = lean_uint64_mix_hash(x_6, x_7);
x_9 = l_Lake_buildO___lambda__1___closed__2;
x_10 = lean_box_uint64(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Lake_BuildTrace_mix(x_2, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = l_Lake_compileO(x_1, x_2, x_3, x_4, x_9, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_11, 1);
lean_ctor_set(x_6, 0, x_15);
lean_ctor_set(x_11, 1, x_6);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
lean_ctor_set(x_6, 0, x_17);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_6);
lean_ctor_set(x_10, 0, x_18);
return x_10;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_22 = x_11;
} else {
 lean_dec_ref(x_11);
 x_22 = lean_box(0);
}
lean_ctor_set(x_6, 0, x_21);
if (lean_is_scalar(x_22)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_22;
}
lean_ctor_set(x_23, 0, x_20);
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
x_25 = !lean_is_exclusive(x_10);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_10, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_11);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_11, 1);
lean_ctor_set(x_6, 0, x_28);
lean_ctor_set(x_11, 1, x_6);
return x_10;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_11, 0);
x_30 = lean_ctor_get(x_11, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_11);
lean_ctor_set(x_6, 0, x_30);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_6);
lean_ctor_set(x_10, 0, x_31);
return x_10;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_10, 1);
lean_inc(x_32);
lean_dec(x_10);
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
lean_ctor_set(x_6, 0, x_34);
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(1, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_6);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_32);
return x_37;
}
}
}
else
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_6, 0);
x_39 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
lean_inc(x_38);
lean_dec(x_6);
x_40 = l_Lake_compileO(x_1, x_2, x_3, x_4, x_38, x_7);
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
x_47 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_39);
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
x_55 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_39);
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
LEAN_EXPORT lean_object* l_Lake_buildO___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lake_BuildTrace_mix(x_1, x_7);
x_12 = l_Array_append___rarg(x_2, x_3);
lean_inc(x_4);
x_13 = lean_alloc_closure((void*)(l_Lake_buildO___lambda__2___boxed), 7, 4);
lean_closure_set(x_13, 0, x_4);
lean_closure_set(x_13, 1, x_5);
lean_closure_set(x_13, 2, x_12);
lean_closure_set(x_13, 3, x_6);
lean_inc(x_4);
x_14 = l_Lake_buildFileUnlessUpToDate(x_4, x_11, x_13, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
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
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_15, 0, x_20);
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_28 = x_15;
} else {
 lean_dec_ref(x_15);
 x_28 = lean_box(0);
}
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_4);
lean_ctor_set(x_29, 1, x_26);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_25);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_4);
x_32 = !lean_is_exclusive(x_14);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_14, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
return x_14;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_ctor_get(x_15, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_15);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_14, 0, x_37);
return x_14;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_14, 1);
lean_inc(x_38);
lean_dec(x_14);
x_39 = lean_ctor_get(x_15, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_15, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_41 = x_15;
} else {
 lean_dec_ref(x_15);
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
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_14);
if (x_44 == 0)
{
return x_14;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_14, 0);
x_46 = lean_ctor_get(x_14, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_14);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_closure((void*)(l_Lake_buildO___lambda__3___boxed), 10, 6);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_11);
lean_closure_set(x_13, 5, x_4);
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_14, 0, x_5);
lean_closure_set(x_14, 1, x_13);
x_15 = 1;
lean_inc(x_6);
x_16 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1(x_14, x_15, x_6, x_10, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
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
x_23 = l_String_isEmpty(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; 
x_24 = l_Lake_buildFileAfterDep___rarg___lambda__3___closed__1;
x_25 = lean_string_append(x_24, x_21);
lean_dec(x_21);
x_26 = l_Lake_readTraceFile_x3f___closed__1;
x_27 = lean_string_append(x_25, x_26);
x_28 = 1;
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_array_push(x_31, x_29);
lean_ctor_set(x_20, 0, x_32);
x_33 = lean_box(0);
x_34 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_22, x_33, x_6, x_20, x_19);
lean_dec(x_6);
return x_34;
}
else
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = lean_ctor_get_uint8(x_20, sizeof(void*)*1);
lean_inc(x_35);
lean_dec(x_20);
x_37 = lean_array_push(x_35, x_29);
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_36);
x_39 = lean_box(0);
x_40 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_22, x_39, x_6, x_38, x_19);
lean_dec(x_6);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_21);
x_41 = lean_box(0);
x_42 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_22, x_41, x_6, x_20, x_19);
lean_dec(x_6);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_6);
x_43 = !lean_is_exclusive(x_16);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_16, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_17);
if (x_45 == 0)
{
return x_16;
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
return x_16;
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
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_6);
x_55 = !lean_is_exclusive(x_16);
if (x_55 == 0)
{
return x_16;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_16, 0);
x_57 = lean_ctor_get(x_16, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_16);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_7);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_7);
lean_ctor_set(x_60, 1, x_8);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_7, 0);
x_62 = lean_ctor_get(x_7, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_7);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_8);
return x_64;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildO(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_inc(x_4);
x_9 = lean_alloc_closure((void*)(l_Lake_buildO___lambda__1___boxed), 5, 1);
lean_closure_set(x_9, 0, x_4);
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_10, 0, x_6);
lean_closure_set(x_10, 1, x_9);
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_alloc_closure((void*)(l_Lake_buildO___lambda__4), 8, 6);
lean_closure_set(x_14, 0, x_3);
lean_closure_set(x_14, 1, x_4);
lean_closure_set(x_14, 2, x_1);
lean_closure_set(x_14, 3, x_5);
lean_closure_set(x_14, 4, x_10);
lean_closure_set(x_14, 5, x_7);
x_15 = l_Task_Priority_default;
x_16 = 0;
x_17 = lean_io_map_task(x_14, x_12, x_15, x_16, x_8);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_2, 0, x_19);
lean_ctor_set(x_17, 0, x_2);
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
lean_ctor_set(x_2, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_free_object(x_2);
lean_dec(x_13);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_2, 0);
x_28 = lean_ctor_get(x_2, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_2);
x_29 = lean_alloc_closure((void*)(l_Lake_buildO___lambda__4), 8, 6);
lean_closure_set(x_29, 0, x_3);
lean_closure_set(x_29, 1, x_4);
lean_closure_set(x_29, 2, x_1);
lean_closure_set(x_29, 3, x_5);
lean_closure_set(x_29, 4, x_10);
lean_closure_set(x_29, 5, x_7);
x_30 = l_Task_Priority_default;
x_31 = 0;
x_32 = lean_io_map_task(x_29, x_27, x_30, x_31, x_8);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
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
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_28);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_28);
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_40 = x_32;
} else {
 lean_dec_ref(x_32);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_buildO___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lake_buildO___spec__2(x_1, x_5, x_6, x_7);
lean_dec(x_1);
x_9 = lean_box_uint64(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___at_Lake_buildO___spec__1___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lake_computeArrayHash___at_Lake_buildO___spec__1(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_buildO___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_buildO___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_buildO___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_4, 1);
x_6 = lean_ctor_get(x_5, 1);
x_7 = lean_ctor_get(x_6, 8);
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Array_append___rarg(x_1, x_2);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = l_Lake_compileO(x_3, x_4, x_9, x_5, x_11, x_8);
lean_dec(x_9);
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
lean_ctor_set(x_7, 0, x_17);
lean_ctor_set(x_13, 1, x_7);
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
lean_ctor_set(x_7, 0, x_19);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_7);
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
lean_ctor_set(x_7, 0, x_23);
if (lean_is_scalar(x_24)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_24;
}
lean_ctor_set(x_25, 0, x_22);
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
lean_ctor_set(x_7, 0, x_30);
lean_ctor_set(x_13, 1, x_7);
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
lean_ctor_set(x_7, 0, x_32);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_7);
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
lean_ctor_set(x_7, 0, x_36);
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_7);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_34);
return x_39;
}
}
}
else
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_7, 0);
x_41 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
lean_inc(x_40);
lean_dec(x_7);
x_42 = l_Lake_compileO(x_3, x_4, x_9, x_5, x_40, x_8);
lean_dec(x_9);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
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
x_46 = lean_ctor_get(x_43, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_48 = x_43;
} else {
 lean_dec_ref(x_43);
 x_48 = lean_box(0);
}
x_49 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_41);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_49);
if (lean_is_scalar(x_45)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_45;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_44);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_52 = lean_ctor_get(x_42, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_53 = x_42;
} else {
 lean_dec_ref(x_42);
 x_53 = lean_box(0);
}
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
x_57 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_41);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
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
}
}
}
static lean_object* _init_l_Lake_buildLeanO___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_buildLeanO___lambda__2___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lake_BuildTrace_mix(x_1, x_6);
lean_inc(x_4);
x_11 = lean_alloc_closure((void*)(l_Lake_buildLeanO___lambda__3___boxed), 8, 4);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_4);
lean_closure_set(x_11, 3, x_5);
x_12 = l_Lake_buildLeanO___lambda__4___closed__1;
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_11);
lean_inc(x_4);
x_14 = l_Lake_buildFileUnlessUpToDate(x_4, x_10, x_13, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
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
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_15, 0, x_20);
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_28 = x_15;
} else {
 lean_dec_ref(x_15);
 x_28 = lean_box(0);
}
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_4);
lean_ctor_set(x_29, 1, x_26);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_25);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_4);
x_32 = !lean_is_exclusive(x_14);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_14, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
return x_14;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_ctor_get(x_15, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_15);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_14, 0, x_37);
return x_14;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_14, 1);
lean_inc(x_38);
lean_dec(x_14);
x_39 = lean_ctor_get(x_15, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_15, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_41 = x_15;
} else {
 lean_dec_ref(x_15);
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
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_14);
if (x_44 == 0)
{
return x_14;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_14, 0);
x_46 = lean_ctor_get(x_14, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_14);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_closure((void*)(l_Lake_buildLeanO___lambda__4), 9, 5);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_3);
lean_closure_set(x_12, 4, x_10);
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_13, 0, x_4);
lean_closure_set(x_13, 1, x_12);
x_14 = 1;
lean_inc(x_5);
x_15 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1(x_13, x_14, x_5, x_9, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = l_String_isEmpty(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; uint8_t x_29; 
x_23 = l_Lake_buildFileAfterDep___rarg___lambda__3___closed__1;
x_24 = lean_string_append(x_23, x_20);
lean_dec(x_20);
x_25 = l_Lake_readTraceFile_x3f___closed__1;
x_26 = lean_string_append(x_24, x_25);
x_27 = 1;
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = !lean_is_exclusive(x_19);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_19, 0);
x_31 = lean_array_push(x_30, x_28);
lean_ctor_set(x_19, 0, x_31);
x_32 = lean_box(0);
x_33 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_21, x_32, x_5, x_19, x_18);
lean_dec(x_5);
return x_33;
}
else
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get_uint8(x_19, sizeof(void*)*1);
lean_inc(x_34);
lean_dec(x_19);
x_36 = lean_array_push(x_34, x_28);
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_35);
x_38 = lean_box(0);
x_39 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_21, x_38, x_5, x_37, x_18);
lean_dec(x_5);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_20);
x_40 = lean_box(0);
x_41 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_21, x_40, x_5, x_19, x_18);
lean_dec(x_5);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_15);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_15, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_16);
if (x_44 == 0)
{
return x_15;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_16, 0);
x_46 = lean_ctor_get(x_16, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_16);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_15, 0, x_47);
return x_15;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_15, 1);
lean_inc(x_48);
lean_dec(x_15);
x_49 = lean_ctor_get(x_16, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_16, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_51 = x_16;
} else {
 lean_dec_ref(x_16);
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
x_54 = !lean_is_exclusive(x_15);
if (x_54 == 0)
{
return x_15;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_15, 0);
x_56 = lean_ctor_get(x_15, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_15);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_6);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_6);
lean_ctor_set(x_59, 1, x_7);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_6, 0);
x_61 = lean_ctor_get(x_6, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_6);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_7);
return x_63;
}
}
}
}
static lean_object* _init_l_Lake_buildLeanO___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_buildLeanO___lambda__1___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_4);
x_7 = lean_alloc_closure((void*)(l_Lake_buildO___lambda__1___boxed), 5, 1);
lean_closure_set(x_7, 0, x_4);
x_8 = l_Lake_buildLeanO___closed__1;
x_9 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_7);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_alloc_closure((void*)(l_Lake_buildLeanO___lambda__5), 7, 5);
lean_closure_set(x_13, 0, x_3);
lean_closure_set(x_13, 1, x_4);
lean_closure_set(x_13, 2, x_1);
lean_closure_set(x_13, 3, x_9);
lean_closure_set(x_13, 4, x_5);
x_14 = l_Task_Priority_default;
x_15 = 0;
x_16 = lean_io_map_task(x_13, x_11, x_14, x_15, x_6);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_ctor_set(x_2, 0, x_18);
lean_ctor_set(x_16, 0, x_2);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_16);
lean_ctor_set(x_2, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_free_object(x_2);
lean_dec(x_12);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_2);
x_28 = lean_alloc_closure((void*)(l_Lake_buildLeanO___lambda__5), 7, 5);
lean_closure_set(x_28, 0, x_3);
lean_closure_set(x_28, 1, x_4);
lean_closure_set(x_28, 2, x_1);
lean_closure_set(x_28, 3, x_9);
lean_closure_set(x_28, 4, x_5);
x_29 = l_Task_Priority_default;
x_30 = 0;
x_31 = lean_io_map_task(x_28, x_26, x_29, x_30, x_6);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
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
lean_ctor_set(x_35, 1, x_27);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_27);
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_39 = x_31;
} else {
 lean_dec_ref(x_31);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_buildLeanO___lambda__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_buildLeanO___lambda__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_buildLeanO___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lake_buildStaticLib___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
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
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lake_buildStaticLib___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lake_buildStaticLib___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_4, 1);
x_6 = lean_ctor_get(x_5, 1);
x_7 = lean_ctor_get(x_6, 11);
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = l_Lake_compileStaticLib(x_1, x_2, x_3, x_8, x_6);
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
x_39 = l_Lake_compileStaticLib(x_1, x_2, x_3, x_37, x_6);
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
static lean_object* _init_l_Lake_buildStaticLib___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lambda__1___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lake_BuildTrace_mix(x_1, x_4);
lean_inc(x_2);
x_9 = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lambda__2___boxed), 6, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_3);
x_10 = l_Lake_buildStaticLib___lambda__3___closed__1;
x_11 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_9);
lean_inc(x_2);
x_12 = l_Lake_buildFileUnlessUpToDate(x_2, x_8, x_11, x_5, x_6, x_7);
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
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_13, 0, x_18);
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_12, 0, x_22);
return x_12;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_dec(x_12);
x_24 = lean_ctor_get(x_13, 0);
lean_inc(x_24);
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
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_24);
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
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_12);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_12, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_13);
if (x_32 == 0)
{
return x_12;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_13);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_12, 0, x_35);
return x_12;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_12, 1);
lean_inc(x_36);
lean_dec(x_12);
x_37 = lean_ctor_get(x_13, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_13, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_39 = x_13;
} else {
 lean_dec_ref(x_13);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_36);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_12);
if (x_42 == 0)
{
return x_12;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_12, 0);
x_44 = lean_ctor_get(x_12, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_12);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lambda__3), 7, 3);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_8);
x_11 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_10);
x_12 = 1;
lean_inc(x_3);
x_13 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1(x_11, x_12, x_3, x_7, x_5);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = l_String_isEmpty(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; 
x_21 = l_Lake_buildFileAfterDep___rarg___lambda__3___closed__1;
x_22 = lean_string_append(x_21, x_18);
lean_dec(x_18);
x_23 = l_Lake_readTraceFile_x3f___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = 1;
x_26 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_25);
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_array_push(x_28, x_26);
lean_ctor_set(x_17, 0, x_29);
x_30 = lean_box(0);
x_31 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_19, x_30, x_3, x_17, x_16);
lean_dec(x_3);
return x_31;
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_17, 0);
x_33 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
lean_inc(x_32);
lean_dec(x_17);
x_34 = lean_array_push(x_32, x_26);
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_33);
x_36 = lean_box(0);
x_37 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_19, x_36, x_3, x_35, x_16);
lean_dec(x_3);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_18);
x_38 = lean_box(0);
x_39 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_19, x_38, x_3, x_17, x_16);
lean_dec(x_3);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_13);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_13, 0);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_14);
if (x_42 == 0)
{
return x_13;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_14, 0);
x_44 = lean_ctor_get(x_14, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_14);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_13, 0, x_45);
return x_13;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_13, 1);
lean_inc(x_46);
lean_dec(x_13);
x_47 = lean_ctor_get(x_14, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_14, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_49 = x_14;
} else {
 lean_dec_ref(x_14);
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
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_3);
x_52 = !lean_is_exclusive(x_13);
if (x_52 == 0)
{
return x_13;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_13, 0);
x_54 = lean_ctor_get(x_13, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_13);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_4);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_4);
lean_ctor_set(x_57, 1, x_5);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_4, 0);
x_59 = lean_ctor_get(x_4, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_4);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_5);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = l_Lake_BuildTrace_nil;
x_6 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lake_buildStaticLib___spec__1___rarg___boxed), 4, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = l_Lake_BuildJob_collectArray___rarg(x_2);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lambda__4), 5, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_6);
lean_closure_set(x_11, 2, x_3);
x_12 = l_Task_Priority_default;
x_13 = 0;
x_14 = lean_io_map_task(x_11, x_9, x_12, x_13, x_4);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_ctor_set(x_7, 0, x_16);
lean_ctor_set(x_14, 0, x_7);
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
lean_ctor_set(x_7, 0, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_free_object(x_7);
lean_dec(x_10);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_7);
x_26 = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lambda__4), 5, 3);
lean_closure_set(x_26, 0, x_1);
lean_closure_set(x_26, 1, x_6);
lean_closure_set(x_26, 2, x_3);
x_27 = l_Task_Priority_default;
x_28 = 0;
x_29 = lean_io_map_task(x_26, x_24, x_27, x_28, x_4);
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
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_25);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_25);
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
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lake_buildStaticLib___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_ReaderT_pure___at_Lake_buildStaticLib___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_buildStaticLib___lambda__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_buildStaticLib___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_buildStaticLib(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l_Array_mapMUnsafe_map___at_Lake_compileStaticLib___spec__1(x_10, x_11, x_1);
x_13 = l_Array_append___rarg(x_12, x_2);
x_14 = l_Array_append___rarg(x_13, x_3);
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = l_Lake_compileSharedLib(x_4, x_14, x_5, x_16, x_8);
lean_dec(x_14);
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
lean_ctor_set(x_7, 0, x_22);
lean_ctor_set(x_18, 1, x_7);
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
lean_ctor_set(x_7, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_7);
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
lean_ctor_set(x_7, 0, x_28);
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_7);
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
lean_ctor_set(x_7, 0, x_35);
lean_ctor_set(x_18, 1, x_7);
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
lean_ctor_set(x_7, 0, x_37);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_7);
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
lean_ctor_set(x_7, 0, x_41);
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_7);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_39);
return x_44;
}
}
}
else
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_7, 0);
x_46 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
lean_inc(x_45);
lean_dec(x_7);
x_47 = l_Lake_compileSharedLib(x_4, x_14, x_5, x_45, x_8);
lean_dec(x_14);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
x_51 = lean_ctor_get(x_48, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_53 = x_48;
} else {
 lean_dec_ref(x_48);
 x_53 = lean_box(0);
}
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_46);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
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
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_47, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_58 = x_47;
} else {
 lean_dec_ref(x_47);
 x_58 = lean_box(0);
}
x_59 = lean_ctor_get(x_48, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_48, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_61 = x_48;
} else {
 lean_dec_ref(x_48);
 x_61 = lean_box(0);
}
x_62 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_46);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_59);
lean_ctor_set(x_63, 1, x_62);
if (lean_is_scalar(x_58)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_58;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_57);
return x_64;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lake_BuildTrace_mix(x_1, x_6);
lean_inc(x_5);
x_11 = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lambda__1___boxed), 8, 4);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_4);
lean_closure_set(x_11, 3, x_5);
x_12 = l_Lake_buildLeanO___lambda__4___closed__1;
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_11);
lean_inc(x_5);
x_14 = l_Lake_buildFileUnlessUpToDate(x_5, x_10, x_13, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
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
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_15, 0, x_20);
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_28 = x_15;
} else {
 lean_dec_ref(x_15);
 x_28 = lean_box(0);
}
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_5);
lean_ctor_set(x_29, 1, x_26);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_25);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_5);
x_32 = !lean_is_exclusive(x_14);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_14, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
return x_14;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_ctor_get(x_15, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_15);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_14, 0, x_37);
return x_14;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_14, 1);
lean_inc(x_38);
lean_dec(x_14);
x_39 = lean_ctor_get(x_15, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_15, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_41 = x_15;
} else {
 lean_dec_ref(x_15);
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
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_5);
x_44 = !lean_is_exclusive(x_14);
if (x_44 == 0)
{
return x_14;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_14, 0);
x_46 = lean_ctor_get(x_14, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_14);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lambda__2), 9, 5);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_10);
lean_closure_set(x_12, 2, x_1);
lean_closure_set(x_12, 3, x_2);
lean_closure_set(x_12, 4, x_3);
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_13, 0, x_4);
lean_closure_set(x_13, 1, x_12);
x_14 = 1;
lean_inc(x_5);
x_15 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1(x_13, x_14, x_5, x_9, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = l_String_isEmpty(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; uint8_t x_29; 
x_23 = l_Lake_buildFileAfterDep___rarg___lambda__3___closed__1;
x_24 = lean_string_append(x_23, x_20);
lean_dec(x_20);
x_25 = l_Lake_readTraceFile_x3f___closed__1;
x_26 = lean_string_append(x_24, x_25);
x_27 = 1;
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = !lean_is_exclusive(x_19);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_19, 0);
x_31 = lean_array_push(x_30, x_28);
lean_ctor_set(x_19, 0, x_31);
x_32 = lean_box(0);
x_33 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_21, x_32, x_5, x_19, x_18);
lean_dec(x_5);
return x_33;
}
else
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get_uint8(x_19, sizeof(void*)*1);
lean_inc(x_34);
lean_dec(x_19);
x_36 = lean_array_push(x_34, x_28);
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_35);
x_38 = lean_box(0);
x_39 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_21, x_38, x_5, x_37, x_18);
lean_dec(x_5);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_20);
x_40 = lean_box(0);
x_41 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_21, x_40, x_5, x_19, x_18);
lean_dec(x_5);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_15);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_15, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_16);
if (x_44 == 0)
{
return x_15;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_16, 0);
x_46 = lean_ctor_get(x_16, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_16);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_15, 0, x_47);
return x_15;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_15, 1);
lean_inc(x_48);
lean_dec(x_15);
x_49 = lean_ctor_get(x_16, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_16, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_51 = x_16;
} else {
 lean_dec_ref(x_16);
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
x_54 = !lean_is_exclusive(x_15);
if (x_54 == 0)
{
return x_15;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_15, 0);
x_56 = lean_ctor_get(x_15, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_15);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_6);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_6);
lean_ctor_set(x_59, 1, x_7);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_6, 0);
x_61 = lean_ctor_get(x_6, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_6);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_7);
return x_63;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_inc(x_4);
x_7 = lean_alloc_closure((void*)(l_Lake_buildO___lambda__1___boxed), 5, 1);
lean_closure_set(x_7, 0, x_4);
x_8 = l_Lake_buildLeanO___closed__1;
x_9 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_7);
x_10 = l_Lake_BuildJob_collectArray___rarg(x_2);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lambda__3), 7, 5);
lean_closure_set(x_14, 0, x_3);
lean_closure_set(x_14, 1, x_4);
lean_closure_set(x_14, 2, x_1);
lean_closure_set(x_14, 3, x_9);
lean_closure_set(x_14, 4, x_5);
x_15 = l_Task_Priority_default;
x_16 = 0;
x_17 = lean_io_map_task(x_14, x_12, x_15, x_16, x_6);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_10, 0, x_19);
lean_ctor_set(x_17, 0, x_10);
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
lean_ctor_set(x_10, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_free_object(x_10);
lean_dec(x_13);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_10, 0);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_10);
x_29 = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lambda__3), 7, 5);
lean_closure_set(x_29, 0, x_3);
lean_closure_set(x_29, 1, x_4);
lean_closure_set(x_29, 2, x_1);
lean_closure_set(x_29, 3, x_9);
lean_closure_set(x_29, 4, x_5);
x_30 = l_Task_Priority_default;
x_31 = 0;
x_32 = lean_io_map_task(x_29, x_27, x_30, x_31, x_6);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
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
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_28);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_28);
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_40 = x_32;
} else {
 lean_dec_ref(x_32);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_buildLeanSharedLib___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_buildLeanSharedLib(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Array_append___rarg(x_1, x_2);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = l_Lake_compileExe(x_3, x_4, x_9, x_5, x_11, x_8);
lean_dec(x_9);
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
lean_ctor_set(x_7, 0, x_17);
lean_ctor_set(x_13, 1, x_7);
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
lean_ctor_set(x_7, 0, x_19);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_7);
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
lean_ctor_set(x_7, 0, x_23);
if (lean_is_scalar(x_24)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_24;
}
lean_ctor_set(x_25, 0, x_22);
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
lean_ctor_set(x_7, 0, x_30);
lean_ctor_set(x_13, 1, x_7);
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
lean_ctor_set(x_7, 0, x_32);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_7);
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
lean_ctor_set(x_7, 0, x_36);
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_7);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_34);
return x_39;
}
}
}
else
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_7, 0);
x_41 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
lean_inc(x_40);
lean_dec(x_7);
x_42 = l_Lake_compileExe(x_3, x_4, x_9, x_5, x_40, x_8);
lean_dec(x_9);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
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
x_46 = lean_ctor_get(x_43, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_48 = x_43;
} else {
 lean_dec_ref(x_43);
 x_48 = lean_box(0);
}
x_49 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_41);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_49);
if (lean_is_scalar(x_45)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_45;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_44);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_52 = lean_ctor_get(x_42, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_53 = x_42;
} else {
 lean_dec_ref(x_42);
 x_53 = lean_box(0);
}
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
x_57 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_41);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
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
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lake_BuildTrace_mix(x_1, x_6);
lean_inc(x_4);
x_11 = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lambda__1___boxed), 8, 4);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_4);
lean_closure_set(x_11, 3, x_5);
x_12 = l_Lake_buildLeanO___lambda__4___closed__1;
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_11);
lean_inc(x_4);
x_14 = l_Lake_buildFileUnlessUpToDate(x_4, x_10, x_13, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
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
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_15, 0, x_20);
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_28 = x_15;
} else {
 lean_dec_ref(x_15);
 x_28 = lean_box(0);
}
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_4);
lean_ctor_set(x_29, 1, x_26);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_25);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_4);
x_32 = !lean_is_exclusive(x_14);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_14, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
return x_14;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_ctor_get(x_15, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_15);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_14, 0, x_37);
return x_14;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_14, 1);
lean_inc(x_38);
lean_dec(x_14);
x_39 = lean_ctor_get(x_15, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_15, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_41 = x_15;
} else {
 lean_dec_ref(x_15);
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
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_14);
if (x_44 == 0)
{
return x_14;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_14, 0);
x_46 = lean_ctor_get(x_14, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_14);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lambda__2), 9, 5);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_3);
lean_closure_set(x_12, 4, x_10);
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_13, 0, x_4);
lean_closure_set(x_13, 1, x_12);
x_14 = 1;
lean_inc(x_5);
x_15 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1(x_13, x_14, x_5, x_9, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = l_String_isEmpty(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; uint8_t x_29; 
x_23 = l_Lake_buildFileAfterDep___rarg___lambda__3___closed__1;
x_24 = lean_string_append(x_23, x_20);
lean_dec(x_20);
x_25 = l_Lake_readTraceFile_x3f___closed__1;
x_26 = lean_string_append(x_24, x_25);
x_27 = 1;
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = !lean_is_exclusive(x_19);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_19, 0);
x_31 = lean_array_push(x_30, x_28);
lean_ctor_set(x_19, 0, x_31);
x_32 = lean_box(0);
x_33 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_21, x_32, x_5, x_19, x_18);
lean_dec(x_5);
return x_33;
}
else
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get_uint8(x_19, sizeof(void*)*1);
lean_inc(x_34);
lean_dec(x_19);
x_36 = lean_array_push(x_34, x_28);
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_35);
x_38 = lean_box(0);
x_39 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_21, x_38, x_5, x_37, x_18);
lean_dec(x_5);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_20);
x_40 = lean_box(0);
x_41 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_21, x_40, x_5, x_19, x_18);
lean_dec(x_5);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_15);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_15, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_16);
if (x_44 == 0)
{
return x_15;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_16, 0);
x_46 = lean_ctor_get(x_16, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_16);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_15, 0, x_47);
return x_15;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_15, 1);
lean_inc(x_48);
lean_dec(x_15);
x_49 = lean_ctor_get(x_16, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_16, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_51 = x_16;
} else {
 lean_dec_ref(x_16);
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
x_54 = !lean_is_exclusive(x_15);
if (x_54 == 0)
{
return x_15;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_15, 0);
x_56 = lean_ctor_get(x_15, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_15);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_6);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_6);
lean_ctor_set(x_59, 1, x_7);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_6, 0);
x_61 = lean_ctor_get(x_6, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_6);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_7);
return x_63;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_inc(x_4);
x_7 = lean_alloc_closure((void*)(l_Lake_buildO___lambda__1___boxed), 5, 1);
lean_closure_set(x_7, 0, x_4);
x_8 = l_Lake_buildLeanO___closed__1;
x_9 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_7);
x_10 = l_Lake_BuildJob_collectArray___rarg(x_2);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lambda__3), 7, 5);
lean_closure_set(x_14, 0, x_3);
lean_closure_set(x_14, 1, x_4);
lean_closure_set(x_14, 2, x_1);
lean_closure_set(x_14, 3, x_9);
lean_closure_set(x_14, 4, x_5);
x_15 = l_Task_Priority_default;
x_16 = 0;
x_17 = lean_io_map_task(x_14, x_12, x_15, x_16, x_6);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_10, 0, x_19);
lean_ctor_set(x_17, 0, x_10);
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
lean_ctor_set(x_10, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_free_object(x_10);
lean_dec(x_13);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_10, 0);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_10);
x_29 = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lambda__3), 7, 5);
lean_closure_set(x_29, 0, x_3);
lean_closure_set(x_29, 1, x_4);
lean_closure_set(x_29, 2, x_1);
lean_closure_set(x_29, 3, x_9);
lean_closure_set(x_29, 4, x_5);
x_30 = l_Task_Priority_default;
x_31 = 0;
x_32 = lean_io_map_task(x_29, x_27, x_30, x_31, x_6);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
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
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_28);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_28);
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_40 = x_32;
} else {
 lean_dec_ref(x_32);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_buildLeanExe___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_buildLeanExe(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = l_Lake_compileSharedLib(x_1, x_2, x_3, x_8, x_6);
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
x_39 = l_Lake_compileSharedLib(x_1, x_2, x_3, x_37, x_6);
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
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint64_t x_10; uint64_t x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_10 = l_Lake_computeArrayHash___at_Lake_buildO___spec__1(x_1);
x_11 = l_Lake_platformTrace;
x_12 = lean_uint64_mix_hash(x_10, x_11);
x_13 = l_Lake_buildO___lambda__1___closed__2;
x_14 = lean_box_uint64(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lake_BuildTrace_mix(x_6, x_15);
x_17 = l_Lake_BuildTrace_mix(x_2, x_16);
x_18 = l_Array_append___rarg(x_3, x_4);
x_19 = l_Array_append___rarg(x_18, x_1);
lean_inc(x_5);
x_20 = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLibOfStatic___lambda__1___boxed), 6, 2);
lean_closure_set(x_20, 0, x_5);
lean_closure_set(x_20, 1, x_19);
x_21 = l_Lake_buildLeanO___lambda__4___closed__1;
x_22 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, x_20);
lean_inc(x_5);
x_23 = l_Lake_buildFileUnlessUpToDate(x_5, x_17, x_22, x_7, x_8, x_9);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_5);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_24, 0, x_29);
return x_23;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_24);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_5);
lean_ctor_set(x_32, 1, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_23, 0, x_33);
return x_23;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_23, 1);
lean_inc(x_34);
lean_dec(x_23);
x_35 = lean_ctor_get(x_24, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_24, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_37 = x_24;
} else {
 lean_dec_ref(x_24);
 x_37 = lean_box(0);
}
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_5);
lean_ctor_set(x_38, 1, x_35);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_34);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_5);
x_41 = !lean_is_exclusive(x_23);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_23, 0);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_24);
if (x_43 == 0)
{
return x_23;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_24, 0);
x_45 = lean_ctor_get(x_24, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_24);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_23, 0, x_46);
return x_23;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_23, 1);
lean_inc(x_47);
lean_dec(x_23);
x_48 = lean_ctor_get(x_24, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_24, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_50 = x_24;
} else {
 lean_dec_ref(x_24);
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
else
{
uint8_t x_53; 
lean_dec(x_5);
x_53 = !lean_is_exclusive(x_23);
if (x_53 == 0)
{
return x_23;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_23, 0);
x_55 = lean_ctor_get(x_23, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_23);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("-Wl,--whole-archive", 19);
return x_1;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__1;
x_2 = l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__2;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("-Wl,--no-whole-archive", 22);
return x_1;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("-Wl,-force_load,", 16);
return x_1;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_61; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = l_Lake_sharedLibExt;
lean_inc(x_8);
x_11 = l_System_FilePath_withExtension(x_8, x_10);
x_61 = l_System_Platform_isOSX;
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__3;
x_63 = lean_array_push(x_62, x_8);
x_64 = l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__4;
x_65 = lean_array_push(x_63, x_64);
x_12 = x_65;
goto block_60;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__5;
x_67 = lean_string_append(x_66, x_8);
lean_dec(x_8);
x_68 = l_Lake_readTraceFile_x3f___closed__1;
x_69 = lean_string_append(x_67, x_68);
x_70 = l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__6;
x_71 = lean_array_push(x_70, x_69);
x_12 = x_71;
goto block_60;
}
block_60:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_13 = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLibOfStatic___lambda__2___boxed), 9, 5);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_9);
lean_closure_set(x_13, 2, x_12);
lean_closure_set(x_13, 3, x_2);
lean_closure_set(x_13, 4, x_11);
x_14 = l_Lake_buildLeanO___closed__1;
x_15 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_13);
x_16 = 1;
lean_inc(x_3);
x_17 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1(x_15, x_16, x_3, x_7, x_5);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = l_String_isEmpty(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; uint8_t x_31; 
x_25 = l_Lake_buildFileAfterDep___rarg___lambda__3___closed__1;
x_26 = lean_string_append(x_25, x_22);
lean_dec(x_22);
x_27 = l_Lake_readTraceFile_x3f___closed__1;
x_28 = lean_string_append(x_26, x_27);
x_29 = 1;
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_29);
x_31 = !lean_is_exclusive(x_21);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_21, 0);
x_33 = lean_array_push(x_32, x_30);
lean_ctor_set(x_21, 0, x_33);
x_34 = lean_box(0);
x_35 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_23, x_34, x_3, x_21, x_20);
lean_dec(x_3);
return x_35;
}
else
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get_uint8(x_21, sizeof(void*)*1);
lean_inc(x_36);
lean_dec(x_21);
x_38 = lean_array_push(x_36, x_30);
x_39 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_37);
x_40 = lean_box(0);
x_41 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_23, x_40, x_3, x_39, x_20);
lean_dec(x_3);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_22);
x_42 = lean_box(0);
x_43 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_23, x_42, x_3, x_21, x_20);
lean_dec(x_3);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_17);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_17, 0);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_18);
if (x_46 == 0)
{
return x_17;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_18, 0);
x_48 = lean_ctor_get(x_18, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_18);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_17, 0, x_49);
return x_17;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_17, 1);
lean_inc(x_50);
lean_dec(x_17);
x_51 = lean_ctor_get(x_18, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_18, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_53 = x_18;
} else {
 lean_dec_ref(x_18);
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
lean_dec(x_3);
x_56 = !lean_is_exclusive(x_17);
if (x_56 == 0)
{
return x_17;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_17, 0);
x_58 = lean_ctor_get(x_17, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_17);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_4);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_4);
lean_ctor_set(x_73, 1, x_5);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_4, 0);
x_75 = lean_ctor_get(x_4, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_4);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_5);
return x_77;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLibOfStatic___lambda__3), 5, 3);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_4);
x_10 = l_Task_Priority_default;
x_11 = 0;
x_12 = lean_io_map_task(x_9, x_7, x_10, x_11, x_5);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_1, 0, x_14);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_free_object(x_1);
lean_dec(x_8);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_24 = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLibOfStatic___lambda__3), 5, 3);
lean_closure_set(x_24, 0, x_3);
lean_closure_set(x_24, 1, x_2);
lean_closure_set(x_24, 2, x_4);
x_25 = l_Task_Priority_default;
x_26 = 0;
x_27 = lean_io_map_task(x_24, x_22, x_25, x_26, x_5);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
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
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_23);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_23);
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_35 = x_27;
} else {
 lean_dec_ref(x_27);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(1, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_buildLeanSharedLibOfStatic___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_buildLeanSharedLibOfStatic___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_computeDynlibOfShared___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_computeDynlibOfShared___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_computeDynlibOfShared___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_computeDynlibOfShared___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__1;
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
x_17 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_computeDynlibOfShared___spec__2), 5, 2);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_1);
x_18 = l_IO_withStdin___at_Lake_computeDynlibOfShared___spec__3(x_15, x_17, x_3, x_4, x_14);
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
x_32 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__5;
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
x_35 = lean_string_from_utf8_unchecked(x_30);
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
x_41 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__5;
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
x_45 = lean_string_from_utf8_unchecked(x_39);
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
x_61 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__5;
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
x_65 = lean_string_from_utf8_unchecked(x_59);
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
x_83 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__5;
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
x_88 = lean_string_from_utf8_unchecked(x_81);
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
x_112 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lake_computeDynlibOfShared___spec__4), 5, 2);
lean_closure_set(x_112, 0, x_16);
lean_closure_set(x_112, 1, x_1);
x_113 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_computeDynlibOfShared___spec__2), 5, 2);
lean_closure_set(x_113, 0, x_16);
lean_closure_set(x_113, 1, x_112);
x_114 = l_IO_withStdin___at_Lake_computeDynlibOfShared___spec__3(x_15, x_113, x_3, x_4, x_14);
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
x_128 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__5;
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
x_131 = lean_string_from_utf8_unchecked(x_126);
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
x_137 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__5;
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
x_141 = lean_string_from_utf8_unchecked(x_135);
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
x_157 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__5;
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
x_161 = lean_string_from_utf8_unchecked(x_155);
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
x_179 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__5;
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
x_184 = lean_string_from_utf8_unchecked(x_177);
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
x_218 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__1;
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
x_228 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_computeDynlibOfShared___spec__2), 5, 2);
lean_closure_set(x_228, 0, x_227);
lean_closure_set(x_228, 1, x_1);
x_229 = l_IO_withStdin___at_Lake_computeDynlibOfShared___spec__3(x_226, x_228, x_3, x_225, x_224);
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
x_245 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__5;
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
x_250 = lean_string_from_utf8_unchecked(x_243);
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
x_269 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lake_computeDynlibOfShared___spec__4), 5, 2);
lean_closure_set(x_269, 0, x_227);
lean_closure_set(x_269, 1, x_1);
x_270 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_computeDynlibOfShared___spec__2), 5, 2);
lean_closure_set(x_270, 0, x_227);
lean_closure_set(x_270, 1, x_269);
x_271 = l_IO_withStdin___at_Lake_computeDynlibOfShared___spec__3(x_226, x_270, x_3, x_225, x_224);
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
x_287 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__5;
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
x_292 = lean_string_from_utf8_unchecked(x_285);
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
LEAN_EXPORT lean_object* l_Lake_computeDynlibOfShared___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; uint8_t x_7; 
x_5 = 3;
x_6 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set_uint8(x_6, sizeof(void*)*1, x_5);
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_array_get_size(x_8);
x_10 = lean_array_push(x_8, x_6);
lean_ctor_set(x_3, 0, x_10);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
lean_inc(x_13);
lean_dec(x_3);
x_15 = lean_array_get_size(x_13);
x_16 = lean_array_push(x_13, x_6);
x_17 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_14);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_4);
return x_19;
}
}
}
static lean_object* _init_l_Lake_computeDynlibOfShared___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("shared library `", 16);
return x_1;
}
}
static lean_object* _init_l_Lake_computeDynlibOfShared___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("` has no file name", 18);
return x_1;
}
}
static lean_object* _init_l_Lake_computeDynlibOfShared___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lib", 3);
return x_1;
}
}
static lean_object* _init_l_Lake_computeDynlibOfShared___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("` does not start with `lib`; this is not supported on Unix", 58);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_computeDynlibOfShared___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_52; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_4);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_4, 0);
x_54 = lean_ctor_get(x_4, 1);
lean_inc(x_53);
x_55 = l_System_FilePath_fileStem(x_53);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_free_object(x_4);
lean_dec(x_54);
x_56 = l_Lake_computeDynlibOfShared___lambda__2___closed__1;
x_57 = lean_string_append(x_56, x_53);
lean_dec(x_53);
x_58 = l_Lake_computeDynlibOfShared___lambda__2___closed__2;
x_59 = lean_string_append(x_57, x_58);
x_60 = lean_alloc_closure((void*)(l_Lake_computeDynlibOfShared___lambda__1___boxed), 4, 1);
lean_closure_set(x_60, 0, x_59);
x_6 = x_60;
goto block_51;
}
else
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_55, 0);
lean_inc(x_61);
lean_dec(x_55);
x_62 = l_System_Platform_isWindows;
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = l_Lake_computeDynlibOfShared___lambda__2___closed__3;
lean_inc(x_61);
x_64 = l_String_startsWith(x_61, x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_61);
lean_free_object(x_4);
lean_dec(x_54);
x_65 = l_Lake_computeDynlibOfShared___lambda__2___closed__1;
x_66 = lean_string_append(x_65, x_53);
lean_dec(x_53);
x_67 = l_Lake_computeDynlibOfShared___lambda__2___closed__4;
x_68 = lean_string_append(x_66, x_67);
x_69 = lean_alloc_closure((void*)(l_Lake_computeDynlibOfShared___lambda__1___boxed), 4, 1);
lean_closure_set(x_69, 0, x_68);
x_6 = x_69;
goto block_51;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_unsigned_to_nat(3u);
x_71 = l_String_drop(x_61, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_53);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_4, 0, x_72);
x_73 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lake_buildStaticLib___spec__1___rarg___boxed), 4, 1);
lean_closure_set(x_73, 0, x_4);
x_6 = x_73;
goto block_51;
}
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_53);
lean_ctor_set(x_74, 1, x_61);
lean_ctor_set(x_4, 0, x_74);
x_75 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lake_buildStaticLib___spec__1___rarg___boxed), 4, 1);
lean_closure_set(x_75, 0, x_4);
x_6 = x_75;
goto block_51;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_4, 0);
x_77 = lean_ctor_get(x_4, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_4);
lean_inc(x_76);
x_78 = l_System_FilePath_fileStem(x_76);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_77);
x_79 = l_Lake_computeDynlibOfShared___lambda__2___closed__1;
x_80 = lean_string_append(x_79, x_76);
lean_dec(x_76);
x_81 = l_Lake_computeDynlibOfShared___lambda__2___closed__2;
x_82 = lean_string_append(x_80, x_81);
x_83 = lean_alloc_closure((void*)(l_Lake_computeDynlibOfShared___lambda__1___boxed), 4, 1);
lean_closure_set(x_83, 0, x_82);
x_6 = x_83;
goto block_51;
}
else
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_78, 0);
lean_inc(x_84);
lean_dec(x_78);
x_85 = l_System_Platform_isWindows;
if (x_85 == 0)
{
lean_object* x_86; uint8_t x_87; 
x_86 = l_Lake_computeDynlibOfShared___lambda__2___closed__3;
lean_inc(x_84);
x_87 = l_String_startsWith(x_84, x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_84);
lean_dec(x_77);
x_88 = l_Lake_computeDynlibOfShared___lambda__2___closed__1;
x_89 = lean_string_append(x_88, x_76);
lean_dec(x_76);
x_90 = l_Lake_computeDynlibOfShared___lambda__2___closed__4;
x_91 = lean_string_append(x_89, x_90);
x_92 = lean_alloc_closure((void*)(l_Lake_computeDynlibOfShared___lambda__1___boxed), 4, 1);
lean_closure_set(x_92, 0, x_91);
x_6 = x_92;
goto block_51;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_unsigned_to_nat(3u);
x_94 = l_String_drop(x_84, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_76);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_77);
x_97 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lake_buildStaticLib___spec__1___rarg___boxed), 4, 1);
lean_closure_set(x_97, 0, x_96);
x_6 = x_97;
goto block_51;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_76);
lean_ctor_set(x_98, 1, x_84);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_77);
x_100 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lake_buildStaticLib___spec__1___rarg___boxed), 4, 1);
lean_closure_set(x_100, 0, x_99);
x_6 = x_100;
goto block_51;
}
}
}
block_51:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 1;
lean_inc(x_1);
x_8 = l_IO_FS_withIsolatedStreams___at_Lake_computeDynlibOfShared___spec__1(x_6, x_7, x_1, x_5, x_3);
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
x_16 = l_Lake_buildFileAfterDep___rarg___lambda__3___closed__1;
x_17 = lean_string_append(x_16, x_13);
lean_dec(x_13);
x_18 = l_Lake_readTraceFile_x3f___closed__1;
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
x_26 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_14, x_25, x_1, x_12, x_11);
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
x_32 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_14, x_31, x_1, x_30, x_11);
lean_dec(x_1);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_13);
x_33 = lean_box(0);
x_34 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_14, x_33, x_1, x_12, x_11);
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
uint8_t x_101; 
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_2);
if (x_101 == 0)
{
lean_object* x_102; 
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_2);
lean_ctor_set(x_102, 1, x_3);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_2, 0);
x_104 = lean_ctor_get(x_2, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_2);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_3);
return x_106;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeDynlibOfShared(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_alloc_closure((void*)(l_Lake_computeDynlibOfShared___lambda__2), 3, 1);
lean_closure_set(x_7, 0, x_2);
x_8 = l_Task_Priority_default;
x_9 = 0;
x_10 = lean_io_map_task(x_7, x_5, x_8, x_9, x_3);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_ctor_set(x_1, 0, x_12);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set(x_1, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_free_object(x_1);
lean_dec(x_6);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = lean_alloc_closure((void*)(l_Lake_computeDynlibOfShared___lambda__2), 3, 1);
lean_closure_set(x_22, 0, x_2);
x_23 = l_Task_Priority_default;
x_24 = 0;
x_25 = lean_io_map_task(x_22, x_20, x_23, x_24, x_3);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
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
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_21);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_21);
x_31 = lean_ctor_get(x_25, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_33 = x_25;
} else {
 lean_dec_ref(x_25);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(1, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_computeDynlibOfShared___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_IO_FS_withIsolatedStreams___at_Lake_computeDynlibOfShared___spec__1(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_computeDynlibOfShared___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_computeDynlibOfShared___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Monad(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Actions(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Common(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Monad(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Actions(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_platformTrace___closed__1 = _init_l_Lake_platformTrace___closed__1();
l_Lake_platformTrace___closed__2 = _init_l_Lake_platformTrace___closed__2();
l_Lake_platformTrace = _init_l_Lake_platformTrace();
l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__1 = _init_l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__1();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__1);
l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__2 = _init_l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__2();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__2);
l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__3 = _init_l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__3();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__3);
l_Lake_instToJsonBuildMetadata___closed__1 = _init_l_Lake_instToJsonBuildMetadata___closed__1();
lean_mark_persistent(l_Lake_instToJsonBuildMetadata___closed__1);
l_Lake_instToJsonBuildMetadata = _init_l_Lake_instToJsonBuildMetadata();
lean_mark_persistent(l_Lake_instToJsonBuildMetadata);
l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__1___closed__1 = _init_l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__1___closed__1();
lean_mark_persistent(l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__1___closed__1);
l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__1___closed__2 = _init_l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__1___closed__2();
lean_mark_persistent(l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__1___closed__2);
l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__1___closed__3 = _init_l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__1___closed__3();
lean_mark_persistent(l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__1___closed__3);
l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__2___closed__1 = _init_l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__2___closed__1();
lean_mark_persistent(l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__2___closed__1);
l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__2___closed__2 = _init_l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__2___closed__2();
lean_mark_persistent(l_Lean_Json_getObjValAs_x3f___at___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____spec__2___closed__2);
l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__1 = _init_l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__1();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__1);
l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__2 = _init_l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__2();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__2);
l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__3 = _init_l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__3();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__3);
l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__4 = _init_l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__4();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__4);
l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__5 = _init_l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__5();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__5);
l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__6 = _init_l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__6();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__6);
l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__7 = _init_l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__7();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__7);
l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__8 = _init_l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__8();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__8);
l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__9 = _init_l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__9();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__9);
l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__10 = _init_l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__10();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__10);
l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__11 = _init_l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__11();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__11);
l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__12 = _init_l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__12();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__12);
l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__13 = _init_l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__13();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__13);
l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__14 = _init_l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__14();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__14);
l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__15 = _init_l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__15();
lean_mark_persistent(l___private_Lake_Build_Common_0__Lake_fromJsonBuildMetadata____x40_Lake_Build_Common___hyg_79____closed__15);
l_Lake_instFromJsonBuildMetadata___closed__1 = _init_l_Lake_instFromJsonBuildMetadata___closed__1();
lean_mark_persistent(l_Lake_instFromJsonBuildMetadata___closed__1);
l_Lake_instFromJsonBuildMetadata = _init_l_Lake_instFromJsonBuildMetadata();
lean_mark_persistent(l_Lake_instFromJsonBuildMetadata);
l_Lake_readTraceFile_x3f___closed__1 = _init_l_Lake_readTraceFile_x3f___closed__1();
lean_mark_persistent(l_Lake_readTraceFile_x3f___closed__1);
l_Lake_readTraceFile_x3f___closed__2 = _init_l_Lake_readTraceFile_x3f___closed__2();
lean_mark_persistent(l_Lake_readTraceFile_x3f___closed__2);
l_Lake_readTraceFile_x3f___closed__3 = _init_l_Lake_readTraceFile_x3f___closed__3();
lean_mark_persistent(l_Lake_readTraceFile_x3f___closed__3);
l_Lake_buildUnlessUpToDate_x3f___rarg___lambda__1___closed__1 = _init_l_Lake_buildUnlessUpToDate_x3f___rarg___lambda__1___closed__1();
l_Lake_buildUnlessUpToDate_x3f___rarg___closed__1 = _init_l_Lake_buildUnlessUpToDate_x3f___rarg___closed__1();
lean_mark_persistent(l_Lake_buildUnlessUpToDate_x3f___rarg___closed__1);
l_Lake_buildUnlessUpToDate_x3f___rarg___closed__2 = _init_l_Lake_buildUnlessUpToDate_x3f___rarg___closed__2();
lean_mark_persistent(l_Lake_buildUnlessUpToDate_x3f___rarg___closed__2);
l_Lake_buildUnlessUpToDate_x3f___rarg___closed__3 = _init_l_Lake_buildUnlessUpToDate_x3f___rarg___closed__3();
lean_mark_persistent(l_Lake_buildUnlessUpToDate_x3f___rarg___closed__3);
l_Lake_cacheFileHash___closed__1 = _init_l_Lake_cacheFileHash___closed__1();
lean_mark_persistent(l_Lake_cacheFileHash___closed__1);
l_Lake_buildFileUnlessUpToDate___closed__1 = _init_l_Lake_buildFileUnlessUpToDate___closed__1();
lean_mark_persistent(l_Lake_buildFileUnlessUpToDate___closed__1);
l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__1 = _init_l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__1();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__1);
l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__2 = _init_l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__2();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__2);
l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__3 = _init_l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__3();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__3);
l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__4 = _init_l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__4();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__4);
l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__5 = _init_l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__5();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__5);
l_Lake_buildFileAfterDep___rarg___lambda__3___closed__1 = _init_l_Lake_buildFileAfterDep___rarg___lambda__3___closed__1();
lean_mark_persistent(l_Lake_buildFileAfterDep___rarg___lambda__3___closed__1);
l_Lake_inputBinFile___closed__1 = _init_l_Lake_inputBinFile___closed__1();
lean_mark_persistent(l_Lake_inputBinFile___closed__1);
l_Lake_buildO___lambda__1___closed__1 = _init_l_Lake_buildO___lambda__1___closed__1();
lean_mark_persistent(l_Lake_buildO___lambda__1___closed__1);
l_Lake_buildO___lambda__1___closed__2 = _init_l_Lake_buildO___lambda__1___closed__2();
lean_mark_persistent(l_Lake_buildO___lambda__1___closed__2);
l_Lake_buildLeanO___lambda__4___closed__1 = _init_l_Lake_buildLeanO___lambda__4___closed__1();
lean_mark_persistent(l_Lake_buildLeanO___lambda__4___closed__1);
l_Lake_buildLeanO___closed__1 = _init_l_Lake_buildLeanO___closed__1();
lean_mark_persistent(l_Lake_buildLeanO___closed__1);
l_Lake_buildStaticLib___lambda__3___closed__1 = _init_l_Lake_buildStaticLib___lambda__3___closed__1();
lean_mark_persistent(l_Lake_buildStaticLib___lambda__3___closed__1);
l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__1 = _init_l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__1();
lean_mark_persistent(l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__1);
l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__2 = _init_l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__2();
lean_mark_persistent(l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__2);
l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__3 = _init_l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__3();
lean_mark_persistent(l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__3);
l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__4 = _init_l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__4();
lean_mark_persistent(l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__4);
l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__5 = _init_l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__5();
lean_mark_persistent(l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__5);
l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__6 = _init_l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__6();
lean_mark_persistent(l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__6);
l_Lake_computeDynlibOfShared___lambda__2___closed__1 = _init_l_Lake_computeDynlibOfShared___lambda__2___closed__1();
lean_mark_persistent(l_Lake_computeDynlibOfShared___lambda__2___closed__1);
l_Lake_computeDynlibOfShared___lambda__2___closed__2 = _init_l_Lake_computeDynlibOfShared___lambda__2___closed__2();
lean_mark_persistent(l_Lake_computeDynlibOfShared___lambda__2___closed__2);
l_Lake_computeDynlibOfShared___lambda__2___closed__3 = _init_l_Lake_computeDynlibOfShared___lambda__2___closed__3();
lean_mark_persistent(l_Lake_computeDynlibOfShared___lambda__2___closed__3);
l_Lake_computeDynlibOfShared___lambda__2___closed__4 = _init_l_Lake_computeDynlibOfShared___lambda__2___closed__4();
lean_mark_persistent(l_Lake_computeDynlibOfShared___lambda__2___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

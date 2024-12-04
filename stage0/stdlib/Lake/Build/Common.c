// Lean compiler output
// Module: Lake.Build.Common
// Imports: Lake.Config.Monad Lake.Build.Actions Lake.Util.JsonObject
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
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__15;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_MTime_instOrd;
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__16;
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_readTraceFile_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_compileO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31_(lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__12;
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__8;
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileHash(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* lean_io_remove_file(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Array_foldlMUnsafe_fold___at_Lake_buildO___spec__1(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepList(lean_object*);
static lean_object* l_Lake_buildO___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lake_buildO___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_get_set_stdout(lean_object*, lean_object*);
static lean_object* l_Lake_computeDynlibOfShared___lambda__2___closed__1;
lean_object* l_Lake_compileSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__1;
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepList___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern uint8_t l_System_Platform_isOSX;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_computeDynlibOfShared___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_inputBinFile___closed__1;
static uint64_t l_Lake_platformTrace___closed__1;
lean_object* l_Lake_MTime_checkUpToDate___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
static uint64_t l_Lake_platformTrace___closed__2;
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at_Lake_inputTextFile___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_buildFileUnlessUpToDate___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lake_instOrdJobAction;
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__6;
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableRelLt___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__5;
lean_object* l_Lake_Hash_ofString_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_instBEqHash;
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
static lean_object* l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__4;
LEAN_EXPORT lean_object* l_Lake_buildStaticLib(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_readTraceFile_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lake_BuildTrace_mix(lean_object*, lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_buildFileUnlessUpToDate___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_compileExe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lake_buildFileUnlessUpToDate___spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildUnlessUpToDate_x3f___rarg___closed__3;
static lean_object* l_Lake_readTraceFile_x3f___closed__2;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_sharedLibExt;
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofHash(uint64_t);
LEAN_EXPORT uint64_t l_Lake_platformTrace;
LEAN_EXPORT lean_object* l_Lake_inputBinFile(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepArray(lean_object*);
static lean_object* l_Lake_buildStaticLib___lambda__3___closed__1;
static lean_object* l_Lake_buildO___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_createParentDirs(lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_buildFileAfterDep___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJson_x3f___lambda__1(lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
LEAN_EXPORT lean_object* l_Lake_computeDynlibOfShared___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__1;
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lake_buildStaticLib___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFromJsonBuildMetadata;
lean_object* l_Lake_BuildJob_collectArray___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__4;
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___rarg___lambda__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lake_computeDynlibOfShared___lambda__2___closed__5;
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_computeDynlibOfShared___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lake_instToJsonLog___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofHash___boxed(lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__3;
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___at_Lake_buildFileUnlessUpToDate___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lambda__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_panic___at_String_fromUTF8_x21___spec__1(lean_object*);
static lean_object* l_Lake_buildUnlessUpToDate_x3f___rarg___closed__1;
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__17;
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_cacheFileHash(lean_object*, lean_object*);
lean_object* l_System_FilePath_fileStem(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_cacheFileHash___closed__1;
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__4;
extern lean_object* l_Task_Priority_default;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_computeDynlibOfShared___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
static lean_object* l_Lake_computeDynlibOfShared___lambda__2___closed__6;
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instMonadBaseIO;
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1(lean_object*, lean_object*);
static lean_object* l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__3;
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lake_buildFileUnlessUpToDate___spec__5(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_bignumFromJson_x3f(lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__13;
extern lean_object* l_Lake_BuildTrace_nil;
static uint64_t l_Lake_buildO___lambda__1___closed__3;
static lean_object* l_Lake_buildLeanO___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJson_x3f___lambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_get_set_stderr(lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__2;
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_computeDynlibOfShared___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lake_buildStaticLib___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lake_compileStaticLib___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_buildFileAfterDep___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildO___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lake_buildStaticLib___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_computeDynlibOfShared___lambda__2___closed__4;
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildUnlessUpToDate_x3f___rarg___closed__2;
lean_object* l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__2;
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_buildFileAfterDep___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_flatMapTR_go___at___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_40____spec__2(lean_object*, lean_object*);
static lean_object* l_Lake_computeDynlibOfShared___lambda__2___closed__7;
lean_object* l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeDynlibOfShared(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildLeanO___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate___spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepArray___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instToJsonBuildMetadata___closed__1;
LEAN_EXPORT lean_object* l_Lake_inputBinFile___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Hash_load_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instFromJsonBuildMetadata___closed__1;
LEAN_EXPORT lean_object* l_Lake_inputFile(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__3(lean_object*, lean_object*, lean_object*);
static uint8_t l_Lake_buildUnlessUpToDate_x3f_go___closed__1;
static lean_object* l_Lake_readTraceFile_x3f___closed__3;
lean_object* l_Std_Internal_Parsec_String_Parser_run___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at_Lake_inputBinFile___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepArray___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lambda__1___closed__4___boxed__const__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern uint64_t l_Lake_Hash_nil;
lean_object* l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeDynlibOfShared___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_computeDynlibOfShared___lambda__2___closed__3;
lean_object* l_Array_mapMUnsafe_map___at_Lake_instFromJsonLog___spec__1(size_t, size_t, lean_object*);
lean_object* lean_io_exit(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lambda__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableRelLe___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lake_writeTraceFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepList___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at_Lake_inputTextFile___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_buildO___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stdin(lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__5;
LEAN_EXPORT lean_object* l_Lake_buildO___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_computeDynlibOfShared___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_checkHashUpToDate___at_Lake_buildFileUnlessUpToDate___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_LeanInstall_ccLinkFlags(uint8_t, lean_object*);
lean_object* l_Lean_Json_Parser_any(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_bignumToJson(lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputBinFile___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lake_instToJsonBuildMetadata;
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_buildFileUnlessUpToDate___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__11;
LEAN_EXPORT lean_object* l_Lake_computeDynlibOfShared___lambda__2(lean_object*, lean_object*, lean_object*);
uint8_t l_Substring_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_buildO___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_computeDynlibOfShared___lambda__2___closed__2;
lean_object* l_Lake_compileStaticLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_writeTraceFile(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_computeBinFileHash(lean_object*, lean_object*);
static lean_object* l_Lake_buildFileUnlessUpToDate___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern uint32_t l_Lake_noBuildCode;
LEAN_EXPORT lean_object* l_Lake_buildO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__9;
lean_object* l_Lake_EStateT_instMonad___rarg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__10;
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_readTraceFile_x3f___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
extern lean_object* l_System_Platform_target;
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f(lean_object*);
extern uint8_t l_System_Platform_isWindows;
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__14;
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_inputTextFile___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildO___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_buildFileAfterDep___rarg___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lake_clearFileHash(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildStaticLib___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at_Lake_inputBinFile___spec__1(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
static lean_object* l_Lake_BuildMetadata_fromJson_x3f___closed__7;
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJson_x3f(lean_object*);
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
x_1 = lean_mk_string_unchecked("depHash", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("log", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint64_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
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
x_11 = lean_array_size(x_10);
x_12 = 0;
x_13 = l_Array_mapMUnsafe_map___at_Lake_instToJsonLog___spec__1(x_11, x_12, x_10);
x_14 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__2;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_8);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_18);
x_20 = l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__3;
x_21 = l_List_flatMapTR_go___at___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_40____spec__2(x_19, x_20);
x_22 = l_Lean_Json_mkObj(x_21);
return x_22;
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
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_ofHash(uint64_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__3;
x_3 = lean_box_uint64(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
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
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJson_x3f___lambda__1(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_BuildMetadata_fromJson_x3f___closed__1;
x_2 = l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_BuildMetadata_fromJson_x3f___closed__2;
x_2 = l_Lake_BuildMetadata_fromJson_x3f___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("property not found: ", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_BuildMetadata_fromJson_x3f___closed__5;
x_2 = l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_BuildMetadata_fromJson_x3f___closed__6;
x_2 = l_Lake_BuildMetadata_fromJson_x3f___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_BuildMetadata_fromJson_x3f___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_BuildMetadata_fromJson_x3f___closed__1;
x_2 = l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_BuildMetadata_fromJson_x3f___closed__9;
x_2 = l_Lake_BuildMetadata_fromJson_x3f___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_cstr_to_nat("18446744073709551616");
return x_1;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("value '{j}' is too large for `UInt64`", 37, 37);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_BuildMetadata_fromJson_x3f___closed__10;
x_2 = l_Lake_BuildMetadata_fromJson_x3f___closed__14;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_BuildMetadata_fromJson_x3f___closed__15;
x_2 = l_Lake_BuildMetadata_fromJson_x3f___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_BuildMetadata_fromJson_x3f___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_BuildMetadata_fromJson_x3f___closed__16;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJson_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_9; 
x_9 = l_Lean_Json_getObj_x3f(x_1);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__1;
x_15 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec(x_13);
x_16 = l_Lake_BuildMetadata_fromJson_x3f___closed__8;
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_bignumFromJson_x3f(x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_13);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = l_Lake_BuildMetadata_fromJson_x3f___closed__10;
x_22 = lean_string_append(x_21, x_20);
lean_dec(x_20);
x_23 = l_Lake_BuildMetadata_fromJson_x3f___closed__1;
x_24 = lean_string_append(x_22, x_23);
lean_ctor_set(x_18, 0, x_24);
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
x_26 = l_Lake_BuildMetadata_fromJson_x3f___closed__10;
x_27 = lean_string_append(x_26, x_25);
lean_dec(x_25);
x_28 = l_Lake_BuildMetadata_fromJson_x3f___closed__1;
x_29 = lean_string_append(x_27, x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_18, 0);
lean_inc(x_31);
lean_dec(x_18);
x_32 = l_Lake_BuildMetadata_fromJson_x3f___closed__11;
x_33 = lean_nat_dec_le(x_32, x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_46; lean_object* x_47; 
x_34 = lean_box(0);
x_35 = l_Lake_BuildMetadata_fromJson_x3f___lambda__1(x_31, x_34);
lean_dec(x_31);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
x_46 = l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__2;
x_47 = l_Lean_RBNode_find___at___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___spec__3(x_13, x_46);
lean_dec(x_13);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_box(0);
x_38 = x_48;
goto block_45;
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_47);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_47, 0);
switch (lean_obj_tag(x_50)) {
case 0:
{
lean_object* x_51; 
lean_free_object(x_47);
x_51 = lean_box(0);
x_38 = x_51;
goto block_45;
}
case 4:
{
lean_object* x_52; size_t x_53; size_t x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_array_size(x_52);
x_54 = 0;
x_55 = l_Array_mapMUnsafe_map___at_Lake_instFromJsonLog___spec__1(x_53, x_54, x_52);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
lean_free_object(x_47);
lean_dec(x_37);
lean_dec(x_36);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec(x_55);
x_2 = x_56;
goto block_8;
}
else
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
lean_dec(x_55);
lean_ctor_set(x_47, 0, x_57);
x_38 = x_47;
goto block_45;
}
}
default: 
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_free_object(x_47);
lean_dec(x_37);
lean_dec(x_36);
x_58 = lean_unsigned_to_nat(80u);
x_59 = l_Lean_Json_pretty(x_50, x_58);
x_60 = l_Lake_BuildMetadata_fromJson_x3f___closed__12;
x_61 = lean_string_append(x_60, x_59);
lean_dec(x_59);
x_62 = l_Lake_BuildMetadata_fromJson_x3f___closed__13;
x_63 = lean_string_append(x_61, x_62);
x_2 = x_63;
goto block_8;
}
}
}
else
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_47, 0);
lean_inc(x_64);
lean_dec(x_47);
switch (lean_obj_tag(x_64)) {
case 0:
{
lean_object* x_65; 
x_65 = lean_box(0);
x_38 = x_65;
goto block_45;
}
case 4:
{
lean_object* x_66; size_t x_67; size_t x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_array_size(x_66);
x_68 = 0;
x_69 = l_Array_mapMUnsafe_map___at_Lake_instFromJsonLog___spec__1(x_67, x_68, x_66);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
lean_dec(x_37);
lean_dec(x_36);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec(x_69);
x_2 = x_70;
goto block_8;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_38 = x_72;
goto block_45;
}
}
default: 
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_37);
lean_dec(x_36);
x_73 = lean_unsigned_to_nat(80u);
x_74 = l_Lean_Json_pretty(x_64, x_73);
x_75 = l_Lake_BuildMetadata_fromJson_x3f___closed__12;
x_76 = lean_string_append(x_75, x_74);
lean_dec(x_74);
x_77 = l_Lake_BuildMetadata_fromJson_x3f___closed__13;
x_78 = lean_string_append(x_76, x_77);
x_2 = x_78;
goto block_8;
}
}
}
}
block_45:
{
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = l___private_Lake_Build_Common_0__Lake_toJsonBuildMetadata____x40_Lake_Build_Common___hyg_31____closed__3;
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_39);
if (lean_is_scalar(x_37)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_37;
}
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_42);
if (lean_is_scalar(x_37)) {
 x_44 = lean_alloc_ctor(1, 1, 0);
} else {
 x_44 = x_37;
}
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
else
{
lean_object* x_79; 
lean_dec(x_31);
lean_dec(x_13);
x_79 = l_Lake_BuildMetadata_fromJson_x3f___closed__17;
return x_79;
}
}
}
}
block_8:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lake_BuildMetadata_fromJson_x3f___closed__4;
x_4 = lean_string_append(x_3, x_2);
lean_dec(x_2);
x_5 = l_Lake_BuildMetadata_fromJson_x3f___closed__1;
x_6 = lean_string_append(x_4, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildMetadata_fromJson_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_BuildMetadata_fromJson_x3f___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instFromJsonBuildMetadata___closed__1() {
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
x_1 = l_Lake_instFromJsonBuildMetadata___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_readTraceFile_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": read failed: ", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_readTraceFile_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_Parser_any), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_readTraceFile_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": invalid trace file: ", 22, 22);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_readTraceFile_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_218; 
x_218 = l_IO_FS_readFile(x_1, x_3);
if (lean_obj_tag(x_218) == 0)
{
uint8_t x_219; 
x_219 = !lean_is_exclusive(x_218);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_220 = lean_ctor_get(x_218, 0);
x_221 = lean_ctor_get(x_218, 1);
x_222 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_222, 0, x_220);
x_223 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_218, 1, x_2);
lean_ctor_set(x_218, 0, x_223);
x_4 = x_218;
x_5 = x_221;
goto block_217;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_224 = lean_ctor_get(x_218, 0);
x_225 = lean_ctor_get(x_218, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_218);
x_226 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_226, 0, x_224);
x_227 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_227, 0, x_226);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_2);
x_4 = x_228;
x_5 = x_225;
goto block_217;
}
}
else
{
uint8_t x_229; 
x_229 = !lean_is_exclusive(x_218);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_230 = lean_ctor_get(x_218, 0);
x_231 = lean_ctor_get(x_218, 1);
x_232 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_232, 0, x_230);
x_233 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set_tag(x_218, 0);
lean_ctor_set(x_218, 1, x_2);
lean_ctor_set(x_218, 0, x_233);
x_4 = x_218;
x_5 = x_231;
goto block_217;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_234 = lean_ctor_get(x_218, 0);
x_235 = lean_ctor_get(x_218, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_218);
x_236 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_236, 0, x_234);
x_237 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_237, 0, x_236);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_2);
x_4 = x_238;
x_5 = x_235;
goto block_217;
}
}
block_217:
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
x_21 = l_Lake_BuildMetadata_fromJson_x3f___closed__1;
x_22 = lean_string_append(x_21, x_1);
x_23 = l_Lake_readTraceFile_x3f___closed__1;
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
x_34 = l_Lake_BuildMetadata_fromJson_x3f___closed__1;
x_35 = lean_string_append(x_34, x_1);
x_36 = l_Lake_readTraceFile_x3f___closed__1;
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
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_48 = lean_ctor_get(x_4, 1);
x_49 = lean_ctor_get(x_4, 0);
lean_dec(x_49);
x_50 = lean_ctor_get(x_8, 0);
lean_inc(x_50);
lean_dec(x_8);
x_51 = lean_string_utf8_byte_size(x_50);
x_52 = lean_unsigned_to_nat(0u);
x_53 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_50, x_51, x_52);
x_54 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_50, x_53, x_51);
x_55 = lean_string_utf8_extract(x_50, x_53, x_54);
lean_dec(x_54);
lean_dec(x_53);
x_56 = l_Lake_Hash_ofString_x3f(x_55);
lean_dec(x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = l_Lake_readTraceFile_x3f___closed__2;
x_58 = l_Std_Internal_Parsec_String_Parser_run___rarg(x_57, x_50);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_free_object(x_6);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec(x_58);
x_60 = l_Lake_BuildMetadata_fromJson_x3f___closed__1;
x_61 = lean_string_append(x_60, x_1);
x_62 = l_Lake_readTraceFile_x3f___closed__3;
x_63 = lean_string_append(x_61, x_62);
x_64 = lean_string_append(x_63, x_59);
lean_dec(x_59);
x_65 = lean_string_append(x_64, x_60);
x_66 = 0;
x_67 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_66);
x_68 = lean_array_push(x_48, x_67);
x_69 = lean_box(0);
lean_ctor_set(x_4, 1, x_68);
lean_ctor_set(x_4, 0, x_69);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_4);
lean_ctor_set(x_70, 1, x_5);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_58, 0);
lean_inc(x_71);
lean_dec(x_58);
x_72 = l_Lake_BuildMetadata_fromJson_x3f(x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_free_object(x_6);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec(x_72);
x_74 = l_Lake_BuildMetadata_fromJson_x3f___closed__1;
x_75 = lean_string_append(x_74, x_1);
x_76 = l_Lake_readTraceFile_x3f___closed__3;
x_77 = lean_string_append(x_75, x_76);
x_78 = lean_string_append(x_77, x_73);
lean_dec(x_73);
x_79 = lean_string_append(x_78, x_74);
x_80 = 0;
x_81 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set_uint8(x_81, sizeof(void*)*1, x_80);
x_82 = lean_array_push(x_48, x_81);
x_83 = lean_box(0);
lean_ctor_set(x_4, 1, x_82);
lean_ctor_set(x_4, 0, x_83);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_4);
lean_ctor_set(x_84, 1, x_5);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_72, 0);
lean_inc(x_85);
lean_dec(x_72);
lean_ctor_set(x_6, 0, x_85);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_4);
lean_ctor_set(x_86, 1, x_5);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_50);
lean_free_object(x_6);
x_87 = !lean_is_exclusive(x_56);
if (x_87 == 0)
{
lean_object* x_88; uint64_t x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_56, 0);
x_89 = lean_unbox_uint64(x_88);
lean_dec(x_88);
x_90 = l_Lake_BuildMetadata_ofHash(x_89);
lean_ctor_set(x_56, 0, x_90);
lean_ctor_set(x_4, 0, x_56);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_4);
lean_ctor_set(x_91, 1, x_5);
return x_91;
}
else
{
lean_object* x_92; uint64_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_56, 0);
lean_inc(x_92);
lean_dec(x_56);
x_93 = lean_unbox_uint64(x_92);
lean_dec(x_92);
x_94 = l_Lake_BuildMetadata_ofHash(x_93);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_4, 0, x_95);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_4);
lean_ctor_set(x_96, 1, x_5);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_97 = lean_ctor_get(x_4, 1);
lean_inc(x_97);
lean_dec(x_4);
x_98 = lean_ctor_get(x_8, 0);
lean_inc(x_98);
lean_dec(x_8);
x_99 = lean_string_utf8_byte_size(x_98);
x_100 = lean_unsigned_to_nat(0u);
x_101 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_98, x_99, x_100);
x_102 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_98, x_101, x_99);
x_103 = lean_string_utf8_extract(x_98, x_101, x_102);
lean_dec(x_102);
lean_dec(x_101);
x_104 = l_Lake_Hash_ofString_x3f(x_103);
lean_dec(x_103);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = l_Lake_readTraceFile_x3f___closed__2;
x_106 = l_Std_Internal_Parsec_String_Parser_run___rarg(x_105, x_98);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_free_object(x_6);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_dec(x_106);
x_108 = l_Lake_BuildMetadata_fromJson_x3f___closed__1;
x_109 = lean_string_append(x_108, x_1);
x_110 = l_Lake_readTraceFile_x3f___closed__3;
x_111 = lean_string_append(x_109, x_110);
x_112 = lean_string_append(x_111, x_107);
lean_dec(x_107);
x_113 = lean_string_append(x_112, x_108);
x_114 = 0;
x_115 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set_uint8(x_115, sizeof(void*)*1, x_114);
x_116 = lean_array_push(x_97, x_115);
x_117 = lean_box(0);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_5);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_106, 0);
lean_inc(x_120);
lean_dec(x_106);
x_121 = l_Lake_BuildMetadata_fromJson_x3f(x_120);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_free_object(x_6);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
lean_dec(x_121);
x_123 = l_Lake_BuildMetadata_fromJson_x3f___closed__1;
x_124 = lean_string_append(x_123, x_1);
x_125 = l_Lake_readTraceFile_x3f___closed__3;
x_126 = lean_string_append(x_124, x_125);
x_127 = lean_string_append(x_126, x_122);
lean_dec(x_122);
x_128 = lean_string_append(x_127, x_123);
x_129 = 0;
x_130 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set_uint8(x_130, sizeof(void*)*1, x_129);
x_131 = lean_array_push(x_97, x_130);
x_132 = lean_box(0);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_131);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_5);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_121, 0);
lean_inc(x_135);
lean_dec(x_121);
lean_ctor_set(x_6, 0, x_135);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_6);
lean_ctor_set(x_136, 1, x_97);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_5);
return x_137;
}
}
}
else
{
lean_object* x_138; lean_object* x_139; uint64_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_98);
lean_free_object(x_6);
x_138 = lean_ctor_get(x_104, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 x_139 = x_104;
} else {
 lean_dec_ref(x_104);
 x_139 = lean_box(0);
}
x_140 = lean_unbox_uint64(x_138);
lean_dec(x_138);
x_141 = l_Lake_BuildMetadata_ofHash(x_140);
if (lean_is_scalar(x_139)) {
 x_142 = lean_alloc_ctor(1, 1, 0);
} else {
 x_142 = x_139;
}
lean_ctor_set(x_142, 0, x_141);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_97);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_5);
return x_144;
}
}
}
}
else
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_6, 0);
lean_inc(x_145);
lean_dec(x_6);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
lean_dec(x_145);
if (lean_obj_tag(x_146) == 11)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_146);
x_147 = lean_ctor_get(x_4, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_148 = x_4;
} else {
 lean_dec_ref(x_4);
 x_148 = lean_box(0);
}
x_149 = lean_box(0);
if (lean_is_scalar(x_148)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_148;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_147);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_5);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_152 = lean_ctor_get(x_4, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_153 = x_4;
} else {
 lean_dec_ref(x_4);
 x_153 = lean_box(0);
}
x_154 = l_Lake_BuildMetadata_fromJson_x3f___closed__1;
x_155 = lean_string_append(x_154, x_1);
x_156 = l_Lake_readTraceFile_x3f___closed__1;
x_157 = lean_string_append(x_155, x_156);
x_158 = lean_io_error_to_string(x_146);
x_159 = lean_string_append(x_157, x_158);
lean_dec(x_158);
x_160 = lean_string_append(x_159, x_154);
x_161 = 2;
x_162 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set_uint8(x_162, sizeof(void*)*1, x_161);
x_163 = lean_array_push(x_152, x_162);
x_164 = lean_box(0);
if (lean_is_scalar(x_153)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_153;
}
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_163);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_5);
return x_166;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_167 = lean_ctor_get(x_4, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_168 = x_4;
} else {
 lean_dec_ref(x_4);
 x_168 = lean_box(0);
}
x_169 = lean_ctor_get(x_145, 0);
lean_inc(x_169);
lean_dec(x_145);
x_170 = lean_string_utf8_byte_size(x_169);
x_171 = lean_unsigned_to_nat(0u);
x_172 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_169, x_170, x_171);
x_173 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_169, x_172, x_170);
x_174 = lean_string_utf8_extract(x_169, x_172, x_173);
lean_dec(x_173);
lean_dec(x_172);
x_175 = l_Lake_Hash_ofString_x3f(x_174);
lean_dec(x_174);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = l_Lake_readTraceFile_x3f___closed__2;
x_177 = l_Std_Internal_Parsec_String_Parser_run___rarg(x_176, x_169);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
lean_dec(x_177);
x_179 = l_Lake_BuildMetadata_fromJson_x3f___closed__1;
x_180 = lean_string_append(x_179, x_1);
x_181 = l_Lake_readTraceFile_x3f___closed__3;
x_182 = lean_string_append(x_180, x_181);
x_183 = lean_string_append(x_182, x_178);
lean_dec(x_178);
x_184 = lean_string_append(x_183, x_179);
x_185 = 0;
x_186 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set_uint8(x_186, sizeof(void*)*1, x_185);
x_187 = lean_array_push(x_167, x_186);
x_188 = lean_box(0);
if (lean_is_scalar(x_168)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_168;
}
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_187);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_5);
return x_190;
}
else
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_177, 0);
lean_inc(x_191);
lean_dec(x_177);
x_192 = l_Lake_BuildMetadata_fromJson_x3f(x_191);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
lean_dec(x_192);
x_194 = l_Lake_BuildMetadata_fromJson_x3f___closed__1;
x_195 = lean_string_append(x_194, x_1);
x_196 = l_Lake_readTraceFile_x3f___closed__3;
x_197 = lean_string_append(x_195, x_196);
x_198 = lean_string_append(x_197, x_193);
lean_dec(x_193);
x_199 = lean_string_append(x_198, x_194);
x_200 = 0;
x_201 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set_uint8(x_201, sizeof(void*)*1, x_200);
x_202 = lean_array_push(x_167, x_201);
x_203 = lean_box(0);
if (lean_is_scalar(x_168)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_168;
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_202);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_5);
return x_205;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_206 = lean_ctor_get(x_192, 0);
lean_inc(x_206);
lean_dec(x_192);
x_207 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_207, 0, x_206);
if (lean_is_scalar(x_168)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_168;
}
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_167);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_5);
return x_209;
}
}
}
else
{
lean_object* x_210; lean_object* x_211; uint64_t x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_169);
x_210 = lean_ctor_get(x_175, 0);
lean_inc(x_210);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 x_211 = x_175;
} else {
 lean_dec_ref(x_175);
 x_211 = lean_box(0);
}
x_212 = lean_unbox_uint64(x_210);
lean_dec(x_210);
x_213 = l_Lake_BuildMetadata_ofHash(x_212);
if (lean_is_scalar(x_211)) {
 x_214 = lean_alloc_ctor(1, 1, 0);
} else {
 x_214 = x_211;
}
lean_ctor_set(x_214, 0, x_213);
if (lean_is_scalar(x_168)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_168;
}
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_167);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_5);
return x_216;
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
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lake_writeTraceFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_writeTraceFile(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
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
static uint8_t _init_l_Lake_buildUnlessUpToDate_x3f_go___closed__1() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = l_Lake_noBuildCode;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_107; uint8_t x_108; 
x_107 = lean_ctor_get(x_5, 0);
lean_inc(x_107);
x_108 = lean_ctor_get_uint8(x_107, sizeof(void*)*1 + 2);
lean_dec(x_107);
if (x_108 == 0)
{
uint8_t x_109; 
x_109 = !lean_is_exclusive(x_6);
if (x_109 == 0)
{
uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_110 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_111 = l_Lake_instOrdJobAction;
x_112 = lean_box(x_110);
x_113 = lean_box(x_4);
x_114 = l_instDecidableRelLe___rarg(x_111, x_112, x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_box(0);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_6);
x_8 = x_116;
x_9 = x_7;
goto block_106;
}
else
{
lean_object* x_117; lean_object* x_118; 
lean_ctor_set_uint8(x_6, sizeof(void*)*1, x_4);
x_117 = lean_box(0);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_6);
x_8 = x_118;
x_9 = x_7;
goto block_106;
}
}
else
{
lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_119 = lean_ctor_get(x_6, 0);
x_120 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
lean_inc(x_119);
lean_dec(x_6);
x_121 = l_Lake_instOrdJobAction;
x_122 = lean_box(x_120);
x_123 = lean_box(x_4);
x_124 = l_instDecidableRelLe___rarg(x_121, x_122, x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_125, 0, x_119);
lean_ctor_set_uint8(x_125, sizeof(void*)*1, x_120);
x_126 = lean_box(0);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_125);
x_8 = x_127;
x_9 = x_7;
goto block_106;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_128, 0, x_119);
lean_ctor_set_uint8(x_128, sizeof(void*)*1, x_4);
x_129 = lean_box(0);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_128);
x_8 = x_130;
x_9 = x_7;
goto block_106;
}
}
}
else
{
uint8_t x_131; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_131 = !lean_is_exclusive(x_6);
if (x_131 == 0)
{
lean_object* x_132; uint8_t x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_6, 0);
x_133 = l_Lake_buildUnlessUpToDate_x3f_go___closed__1;
x_134 = lean_io_exit(x_133, x_7);
if (lean_obj_tag(x_134) == 0)
{
uint8_t x_135; 
x_135 = !lean_is_exclusive(x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_134, 0);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_6);
lean_ctor_set(x_134, 0, x_137);
return x_134;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_138 = lean_ctor_get(x_134, 0);
x_139 = lean_ctor_get(x_134, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_134);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_6);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
}
else
{
uint8_t x_142; 
x_142 = !lean_is_exclusive(x_134);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_143 = lean_ctor_get(x_134, 0);
x_144 = lean_io_error_to_string(x_143);
x_145 = 3;
x_146 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set_uint8(x_146, sizeof(void*)*1, x_145);
x_147 = lean_array_get_size(x_132);
x_148 = lean_array_push(x_132, x_146);
lean_ctor_set(x_6, 0, x_148);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_6);
lean_ctor_set_tag(x_134, 0);
lean_ctor_set(x_134, 0, x_149);
return x_134;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_150 = lean_ctor_get(x_134, 0);
x_151 = lean_ctor_get(x_134, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_134);
x_152 = lean_io_error_to_string(x_150);
x_153 = 3;
x_154 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set_uint8(x_154, sizeof(void*)*1, x_153);
x_155 = lean_array_get_size(x_132);
x_156 = lean_array_push(x_132, x_154);
lean_ctor_set(x_6, 0, x_156);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_6);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_151);
return x_158;
}
}
}
else
{
lean_object* x_159; uint8_t x_160; uint8_t x_161; lean_object* x_162; 
x_159 = lean_ctor_get(x_6, 0);
x_160 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
lean_inc(x_159);
lean_dec(x_6);
x_161 = l_Lake_buildUnlessUpToDate_x3f_go___closed__1;
x_162 = lean_io_exit(x_161, x_7);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_165 = x_162;
} else {
 lean_dec_ref(x_162);
 x_165 = lean_box(0);
}
x_166 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_166, 0, x_159);
lean_ctor_set_uint8(x_166, sizeof(void*)*1, x_160);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_163);
lean_ctor_set(x_167, 1, x_166);
if (lean_is_scalar(x_165)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_165;
}
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_164);
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_169 = lean_ctor_get(x_162, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_162, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_171 = x_162;
} else {
 lean_dec_ref(x_162);
 x_171 = lean_box(0);
}
x_172 = lean_io_error_to_string(x_169);
x_173 = 3;
x_174 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set_uint8(x_174, sizeof(void*)*1, x_173);
x_175 = lean_array_get_size(x_159);
x_176 = lean_array_push(x_159, x_174);
x_177 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set_uint8(x_177, sizeof(void*)*1, x_160);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_177);
if (lean_is_scalar(x_171)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_171;
 lean_ctor_set_tag(x_179, 0);
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_170);
return x_179;
}
}
}
block_106:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_array_get_size(x_11);
lean_dec(x_11);
x_13 = lean_apply_3(x_3, x_5, x_10, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_14, 1);
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_array_get_size(x_20);
x_22 = l_Array_extract___rarg(x_20, x_12, x_21);
x_23 = l_Lake_writeTraceFile(x_2, x_1, x_22, x_18);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = 0;
x_27 = lean_box(x_26);
lean_ctor_set(x_14, 0, x_27);
lean_ctor_set(x_23, 0, x_14);
return x_23;
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = 0;
x_30 = lean_box(x_29);
lean_ctor_set(x_14, 0, x_30);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_14);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_23, 0);
x_34 = lean_io_error_to_string(x_33);
x_35 = 3;
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_35);
x_37 = lean_array_push(x_20, x_36);
lean_ctor_set(x_16, 0, x_37);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_21);
lean_ctor_set_tag(x_23, 0);
lean_ctor_set(x_23, 0, x_14);
return x_23;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_23, 0);
x_39 = lean_ctor_get(x_23, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_23);
x_40 = lean_io_error_to_string(x_38);
x_41 = 3;
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
x_43 = lean_array_push(x_20, x_42);
lean_ctor_set(x_16, 0, x_43);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_21);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_14);
lean_ctor_set(x_44, 1, x_39);
return x_44;
}
}
}
else
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_16, 0);
x_46 = lean_ctor_get_uint8(x_16, sizeof(void*)*1);
lean_inc(x_45);
lean_dec(x_16);
x_47 = lean_array_get_size(x_45);
x_48 = l_Array_extract___rarg(x_45, x_12, x_47);
x_49 = l_Lake_writeTraceFile(x_2, x_1, x_48, x_18);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_47);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_51 = x_49;
} else {
 lean_dec_ref(x_49);
 x_51 = lean_box(0);
}
x_52 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_52, 0, x_45);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_46);
x_53 = 0;
x_54 = lean_box(x_53);
lean_ctor_set(x_14, 1, x_52);
lean_ctor_set(x_14, 0, x_54);
if (lean_is_scalar(x_51)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_51;
}
lean_ctor_set(x_55, 0, x_14);
lean_ctor_set(x_55, 1, x_50);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_56 = lean_ctor_get(x_49, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_49, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_58 = x_49;
} else {
 lean_dec_ref(x_49);
 x_58 = lean_box(0);
}
x_59 = lean_io_error_to_string(x_56);
x_60 = 3;
x_61 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_60);
x_62 = lean_array_push(x_45, x_61);
x_63 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_46);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 1, x_63);
lean_ctor_set(x_14, 0, x_47);
if (lean_is_scalar(x_58)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_58;
 lean_ctor_set_tag(x_64, 0);
}
lean_ctor_set(x_64, 0, x_14);
lean_ctor_set(x_64, 1, x_57);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_65 = lean_ctor_get(x_14, 1);
lean_inc(x_65);
lean_dec(x_14);
x_66 = lean_ctor_get(x_13, 1);
lean_inc(x_66);
lean_dec(x_13);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
x_68 = lean_ctor_get_uint8(x_65, sizeof(void*)*1);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 x_69 = x_65;
} else {
 lean_dec_ref(x_65);
 x_69 = lean_box(0);
}
x_70 = lean_array_get_size(x_67);
x_71 = l_Array_extract___rarg(x_67, x_12, x_70);
x_72 = l_Lake_writeTraceFile(x_2, x_1, x_71, x_66);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_70);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_74 = x_72;
} else {
 lean_dec_ref(x_72);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_75 = lean_alloc_ctor(0, 1, 1);
} else {
 x_75 = x_69;
}
lean_ctor_set(x_75, 0, x_67);
lean_ctor_set_uint8(x_75, sizeof(void*)*1, x_68);
x_76 = 0;
x_77 = lean_box(x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
if (lean_is_scalar(x_74)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_74;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_73);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_80 = lean_ctor_get(x_72, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_72, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_82 = x_72;
} else {
 lean_dec_ref(x_72);
 x_82 = lean_box(0);
}
x_83 = lean_io_error_to_string(x_80);
x_84 = 3;
x_85 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set_uint8(x_85, sizeof(void*)*1, x_84);
x_86 = lean_array_push(x_67, x_85);
if (lean_is_scalar(x_69)) {
 x_87 = lean_alloc_ctor(0, 1, 1);
} else {
 x_87 = x_69;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set_uint8(x_87, sizeof(void*)*1, x_68);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_70);
lean_ctor_set(x_88, 1, x_87);
if (lean_is_scalar(x_82)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_82;
 lean_ctor_set_tag(x_89, 0);
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_81);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_12);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_13);
if (x_90 == 0)
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_13, 0);
lean_dec(x_91);
x_92 = !lean_is_exclusive(x_14);
if (x_92 == 0)
{
return x_13;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_14, 0);
x_94 = lean_ctor_get(x_14, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_14);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set(x_13, 0, x_95);
return x_13;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_96 = lean_ctor_get(x_13, 1);
lean_inc(x_96);
lean_dec(x_13);
x_97 = lean_ctor_get(x_14, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_14, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_99 = x_14;
} else {
 lean_dec_ref(x_14);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_96);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_12);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_13);
if (x_102 == 0)
{
return x_13;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_13, 0);
x_104 = lean_ctor_get(x_13, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_13);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lake_buildUnlessUpToDate_x3f_go(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_1 = lean_alloc_closure((void*)(l_Lake_buildUnlessUpToDate_x3f___rarg___lambda__1___boxed), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_364; 
x_364 = !lean_is_exclusive(x_10);
if (x_364 == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; 
x_365 = lean_ctor_get(x_10, 0);
x_366 = l_System_FilePath_pathExists(x_5, x_11);
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
x_368 = lean_unbox(x_367);
lean_dec(x_367);
if (x_368 == 0)
{
uint8_t x_369; 
lean_dec(x_8);
lean_dec(x_1);
x_369 = !lean_is_exclusive(x_366);
if (x_369 == 0)
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; uint8_t x_374; 
x_370 = lean_ctor_get(x_366, 1);
x_371 = lean_ctor_get(x_366, 0);
lean_dec(x_371);
x_372 = lean_ctor_get(x_4, 1);
lean_inc(x_372);
x_373 = l_Lake_MTime_checkUpToDate___rarg(x_2, x_3, x_372, x_370);
x_374 = !lean_is_exclusive(x_373);
if (x_374 == 0)
{
lean_object* x_375; lean_object* x_376; uint8_t x_377; 
x_375 = lean_ctor_get(x_373, 0);
x_376 = lean_ctor_get(x_373, 1);
x_377 = lean_unbox(x_375);
lean_dec(x_375);
if (x_377 == 0)
{
lean_object* x_378; 
lean_free_object(x_373);
lean_free_object(x_366);
x_378 = l_Lake_buildUnlessUpToDate_x3f_go(x_4, x_5, x_6, x_7, x_9, x_10, x_376);
return x_378;
}
else
{
uint8_t x_379; lean_object* x_380; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
x_379 = 1;
x_380 = lean_box(x_379);
lean_ctor_set(x_366, 1, x_10);
lean_ctor_set(x_366, 0, x_380);
lean_ctor_set(x_373, 0, x_366);
return x_373;
}
}
else
{
lean_object* x_381; lean_object* x_382; uint8_t x_383; 
x_381 = lean_ctor_get(x_373, 0);
x_382 = lean_ctor_get(x_373, 1);
lean_inc(x_382);
lean_inc(x_381);
lean_dec(x_373);
x_383 = lean_unbox(x_381);
lean_dec(x_381);
if (x_383 == 0)
{
lean_object* x_384; 
lean_free_object(x_366);
x_384 = l_Lake_buildUnlessUpToDate_x3f_go(x_4, x_5, x_6, x_7, x_9, x_10, x_382);
return x_384;
}
else
{
uint8_t x_385; lean_object* x_386; lean_object* x_387; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
x_385 = 1;
x_386 = lean_box(x_385);
lean_ctor_set(x_366, 1, x_10);
lean_ctor_set(x_366, 0, x_386);
x_387 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_387, 0, x_366);
lean_ctor_set(x_387, 1, x_382);
return x_387;
}
}
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; uint8_t x_394; 
x_388 = lean_ctor_get(x_366, 1);
lean_inc(x_388);
lean_dec(x_366);
x_389 = lean_ctor_get(x_4, 1);
lean_inc(x_389);
x_390 = l_Lake_MTime_checkUpToDate___rarg(x_2, x_3, x_389, x_388);
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_390, 1);
lean_inc(x_392);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 lean_ctor_release(x_390, 1);
 x_393 = x_390;
} else {
 lean_dec_ref(x_390);
 x_393 = lean_box(0);
}
x_394 = lean_unbox(x_391);
lean_dec(x_391);
if (x_394 == 0)
{
lean_object* x_395; 
lean_dec(x_393);
x_395 = l_Lake_buildUnlessUpToDate_x3f_go(x_4, x_5, x_6, x_7, x_9, x_10, x_392);
return x_395;
}
else
{
uint8_t x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
x_396 = 1;
x_397 = lean_box(x_396);
x_398 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_398, 0, x_397);
lean_ctor_set(x_398, 1, x_10);
if (lean_is_scalar(x_393)) {
 x_399 = lean_alloc_ctor(0, 2, 0);
} else {
 x_399 = x_393;
}
lean_ctor_set(x_399, 0, x_398);
lean_ctor_set(x_399, 1, x_392);
return x_399;
}
}
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; uint8_t x_404; 
x_400 = lean_ctor_get(x_366, 1);
lean_inc(x_400);
lean_dec(x_366);
x_401 = l_Lake_readTraceFile_x3f(x_5, x_365, x_400);
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
lean_dec(x_401);
x_404 = !lean_is_exclusive(x_402);
if (x_404 == 0)
{
lean_object* x_405; 
x_405 = lean_ctor_get(x_402, 1);
lean_ctor_set(x_10, 0, x_405);
lean_ctor_set(x_402, 1, x_10);
x_12 = x_402;
x_13 = x_403;
goto block_363;
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_406 = lean_ctor_get(x_402, 0);
x_407 = lean_ctor_get(x_402, 1);
lean_inc(x_407);
lean_inc(x_406);
lean_dec(x_402);
lean_ctor_set(x_10, 0, x_407);
x_408 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_408, 0, x_406);
lean_ctor_set(x_408, 1, x_10);
x_12 = x_408;
x_13 = x_403;
goto block_363;
}
}
}
else
{
lean_object* x_409; uint8_t x_410; lean_object* x_411; lean_object* x_412; uint8_t x_413; 
x_409 = lean_ctor_get(x_10, 0);
x_410 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
lean_inc(x_409);
lean_dec(x_10);
x_411 = l_System_FilePath_pathExists(x_5, x_11);
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_unbox(x_412);
lean_dec(x_412);
if (x_413 == 0)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; 
lean_dec(x_8);
lean_dec(x_1);
x_414 = lean_ctor_get(x_411, 1);
lean_inc(x_414);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 lean_ctor_release(x_411, 1);
 x_415 = x_411;
} else {
 lean_dec_ref(x_411);
 x_415 = lean_box(0);
}
x_416 = lean_ctor_get(x_4, 1);
lean_inc(x_416);
x_417 = l_Lake_MTime_checkUpToDate___rarg(x_2, x_3, x_416, x_414);
x_418 = lean_ctor_get(x_417, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_417, 1);
lean_inc(x_419);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 x_420 = x_417;
} else {
 lean_dec_ref(x_417);
 x_420 = lean_box(0);
}
x_421 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_421, 0, x_409);
lean_ctor_set_uint8(x_421, sizeof(void*)*1, x_410);
x_422 = lean_unbox(x_418);
lean_dec(x_418);
if (x_422 == 0)
{
lean_object* x_423; 
lean_dec(x_420);
lean_dec(x_415);
x_423 = l_Lake_buildUnlessUpToDate_x3f_go(x_4, x_5, x_6, x_7, x_9, x_421, x_419);
return x_423;
}
else
{
uint8_t x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
x_424 = 1;
x_425 = lean_box(x_424);
if (lean_is_scalar(x_415)) {
 x_426 = lean_alloc_ctor(0, 2, 0);
} else {
 x_426 = x_415;
}
lean_ctor_set(x_426, 0, x_425);
lean_ctor_set(x_426, 1, x_421);
if (lean_is_scalar(x_420)) {
 x_427 = lean_alloc_ctor(0, 2, 0);
} else {
 x_427 = x_420;
}
lean_ctor_set(x_427, 0, x_426);
lean_ctor_set(x_427, 1, x_419);
return x_427;
}
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_428 = lean_ctor_get(x_411, 1);
lean_inc(x_428);
lean_dec(x_411);
x_429 = l_Lake_readTraceFile_x3f(x_5, x_409, x_428);
x_430 = lean_ctor_get(x_429, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_429, 1);
lean_inc(x_431);
lean_dec(x_429);
x_432 = lean_ctor_get(x_430, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_430, 1);
lean_inc(x_433);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 x_434 = x_430;
} else {
 lean_dec_ref(x_430);
 x_434 = lean_box(0);
}
x_435 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_435, 0, x_433);
lean_ctor_set_uint8(x_435, sizeof(void*)*1, x_410);
if (lean_is_scalar(x_434)) {
 x_436 = lean_alloc_ctor(0, 2, 0);
} else {
 x_436 = x_434;
}
lean_ctor_set(x_436, 0, x_432);
lean_ctor_set(x_436, 1, x_435);
x_12 = x_436;
x_13 = x_431;
goto block_363;
}
}
block_363:
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_12, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_18, sizeof(void*)*1);
lean_dec(x_18);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lake_MTime_checkUpToDate___rarg(x_2, x_3, x_8, x_13);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
if (x_19 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_free_object(x_21);
lean_dec(x_23);
lean_free_object(x_12);
x_25 = l_Lake_buildUnlessUpToDate_x3f_go(x_4, x_5, x_6, x_7, x_9, x_16, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
x_28 = lean_unbox(x_26);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; 
lean_free_object(x_21);
lean_free_object(x_12);
x_29 = l_Lake_buildUnlessUpToDate_x3f_go(x_4, x_5, x_6, x_7, x_9, x_16, x_27);
return x_29;
}
else
{
uint8_t x_30; lean_object* x_31; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
x_30 = 1;
x_31 = lean_box(x_30);
lean_ctor_set(x_12, 0, x_31);
lean_ctor_set(x_21, 0, x_12);
return x_21;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_21, 0);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_21);
if (x_19 == 0)
{
lean_object* x_34; 
lean_dec(x_32);
lean_free_object(x_12);
x_34 = l_Lake_buildUnlessUpToDate_x3f_go(x_4, x_5, x_6, x_7, x_9, x_16, x_33);
return x_34;
}
else
{
uint8_t x_35; 
x_35 = lean_unbox(x_32);
lean_dec(x_32);
if (x_35 == 0)
{
lean_object* x_36; 
lean_free_object(x_12);
x_36 = l_Lake_buildUnlessUpToDate_x3f_go(x_4, x_5, x_6, x_7, x_9, x_16, x_33);
return x_36;
}
else
{
uint8_t x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
x_37 = 1;
x_38 = lean_box(x_37);
lean_ctor_set(x_12, 0, x_38);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_12);
lean_ctor_set(x_39, 1, x_33);
return x_39;
}
}
}
}
else
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_16, 0);
x_41 = lean_ctor_get_uint8(x_16, sizeof(void*)*1);
lean_inc(x_40);
lean_dec(x_16);
x_42 = l_Lake_MTime_checkUpToDate___rarg(x_2, x_3, x_8, x_13);
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
if (x_19 == 0)
{
lean_object* x_47; 
lean_dec(x_45);
lean_dec(x_43);
lean_free_object(x_12);
x_47 = l_Lake_buildUnlessUpToDate_x3f_go(x_4, x_5, x_6, x_7, x_9, x_46, x_44);
return x_47;
}
else
{
uint8_t x_48; 
x_48 = lean_unbox(x_43);
lean_dec(x_43);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_45);
lean_free_object(x_12);
x_49 = l_Lake_buildUnlessUpToDate_x3f_go(x_4, x_5, x_6, x_7, x_9, x_46, x_44);
return x_49;
}
else
{
uint8_t x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_9);
lean_dec(x_6);
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
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_53 = lean_ctor_get(x_12, 1);
lean_inc(x_53);
lean_dec(x_12);
x_54 = lean_ctor_get(x_9, 0);
lean_inc(x_54);
x_55 = lean_ctor_get_uint8(x_54, sizeof(void*)*1);
lean_dec(x_54);
x_56 = lean_ctor_get(x_53, 0);
lean_inc(x_56);
x_57 = lean_ctor_get_uint8(x_53, sizeof(void*)*1);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_58 = x_53;
} else {
 lean_dec_ref(x_53);
 x_58 = lean_box(0);
}
x_59 = l_Lake_MTime_checkUpToDate___rarg(x_2, x_3, x_8, x_13);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_62 = x_59;
} else {
 lean_dec_ref(x_59);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_63 = lean_alloc_ctor(0, 1, 1);
} else {
 x_63 = x_58;
}
lean_ctor_set(x_63, 0, x_56);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_57);
if (x_55 == 0)
{
lean_object* x_64; 
lean_dec(x_62);
lean_dec(x_60);
x_64 = l_Lake_buildUnlessUpToDate_x3f_go(x_4, x_5, x_6, x_7, x_9, x_63, x_61);
return x_64;
}
else
{
uint8_t x_65; 
x_65 = lean_unbox(x_60);
lean_dec(x_60);
if (x_65 == 0)
{
lean_object* x_66; 
lean_dec(x_62);
x_66 = l_Lake_buildUnlessUpToDate_x3f_go(x_4, x_5, x_6, x_7, x_9, x_63, x_61);
return x_66;
}
else
{
uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
x_67 = 1;
x_68 = lean_box(x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_63);
if (lean_is_scalar(x_62)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_62;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_61);
return x_70;
}
}
}
}
else
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_14);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_14, 0);
x_73 = lean_ctor_get(x_12, 1);
lean_inc(x_73);
lean_dec(x_12);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
lean_ctor_set(x_14, 0, x_74);
lean_inc(x_4);
x_76 = l_Lake_checkHashUpToDate___rarg(x_1, x_2, x_3, x_4, x_14, x_8, x_9, x_73, x_13);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
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
x_80 = !lean_is_exclusive(x_77);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_180; 
x_81 = lean_ctor_get(x_77, 0);
x_82 = lean_ctor_get(x_77, 1);
x_180 = lean_unbox(x_81);
lean_dec(x_81);
if (x_180 == 0)
{
lean_object* x_181; 
lean_free_object(x_77);
lean_dec(x_79);
lean_dec(x_75);
x_181 = l_Lake_buildUnlessUpToDate_x3f_go(x_4, x_5, x_6, x_7, x_9, x_82, x_78);
return x_181;
}
else
{
uint8_t x_182; 
lean_dec(x_6);
lean_dec(x_4);
x_182 = !lean_is_exclusive(x_82);
if (x_182 == 0)
{
uint8_t x_183; lean_object* x_184; uint8_t x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_183 = lean_ctor_get_uint8(x_82, sizeof(void*)*1);
x_184 = l_Lake_instOrdJobAction;
x_185 = 1;
x_186 = lean_box(x_183);
x_187 = lean_box(x_185);
x_188 = l_instDecidableRelLe___rarg(x_184, x_186, x_187);
if (x_188 == 0)
{
lean_object* x_189; 
x_189 = lean_box(0);
lean_ctor_set(x_77, 0, x_189);
x_83 = x_77;
x_84 = x_78;
goto block_179;
}
else
{
lean_object* x_190; 
lean_ctor_set_uint8(x_82, sizeof(void*)*1, x_185);
x_190 = lean_box(0);
lean_ctor_set(x_77, 0, x_190);
x_83 = x_77;
x_84 = x_78;
goto block_179;
}
}
else
{
lean_object* x_191; uint8_t x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
x_191 = lean_ctor_get(x_82, 0);
x_192 = lean_ctor_get_uint8(x_82, sizeof(void*)*1);
lean_inc(x_191);
lean_dec(x_82);
x_193 = l_Lake_instOrdJobAction;
x_194 = 1;
x_195 = lean_box(x_192);
x_196 = lean_box(x_194);
x_197 = l_instDecidableRelLe___rarg(x_193, x_195, x_196);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; 
x_198 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_198, 0, x_191);
lean_ctor_set_uint8(x_198, sizeof(void*)*1, x_192);
x_199 = lean_box(0);
lean_ctor_set(x_77, 1, x_198);
lean_ctor_set(x_77, 0, x_199);
x_83 = x_77;
x_84 = x_78;
goto block_179;
}
else
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_200, 0, x_191);
lean_ctor_set_uint8(x_200, sizeof(void*)*1, x_194);
x_201 = lean_box(0);
lean_ctor_set(x_77, 1, x_200);
lean_ctor_set(x_77, 0, x_201);
x_83 = x_77;
x_84 = x_78;
goto block_179;
}
}
}
block_179:
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_83);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_86 = lean_ctor_get(x_83, 1);
x_87 = lean_ctor_get(x_83, 0);
lean_dec(x_87);
x_88 = lean_array_get_size(x_75);
x_89 = lean_unsigned_to_nat(0u);
x_90 = lean_nat_dec_lt(x_89, x_88);
if (x_90 == 0)
{
uint8_t x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_88);
lean_dec(x_75);
lean_dec(x_9);
x_91 = 1;
x_92 = lean_box(x_91);
lean_ctor_set(x_83, 0, x_92);
if (lean_is_scalar(x_79)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_79;
}
lean_ctor_set(x_93, 0, x_83);
lean_ctor_set(x_93, 1, x_84);
return x_93;
}
else
{
uint8_t x_94; 
x_94 = lean_nat_dec_le(x_88, x_88);
if (x_94 == 0)
{
uint8_t x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_88);
lean_dec(x_75);
lean_dec(x_9);
x_95 = 1;
x_96 = lean_box(x_95);
lean_ctor_set(x_83, 0, x_96);
if (lean_is_scalar(x_79)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_79;
}
lean_ctor_set(x_97, 0, x_83);
lean_ctor_set(x_97, 1, x_84);
return x_97;
}
else
{
size_t x_98; size_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_free_object(x_83);
lean_dec(x_79);
x_98 = 0;
x_99 = lean_usize_of_nat(x_88);
lean_dec(x_88);
x_100 = l_Lake_buildUnlessUpToDate_x3f___rarg___closed__2;
x_101 = l_Lake_buildUnlessUpToDate_x3f___rarg___closed__3;
x_102 = lean_box(0);
x_103 = l_Array_foldlMUnsafe_fold___rarg(x_100, x_101, x_75, x_98, x_99, x_102);
x_104 = lean_apply_3(x_103, x_9, x_86, x_84);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
if (lean_obj_tag(x_105) == 0)
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_104);
if (x_106 == 0)
{
lean_object* x_107; uint8_t x_108; 
x_107 = lean_ctor_get(x_104, 0);
lean_dec(x_107);
x_108 = !lean_is_exclusive(x_105);
if (x_108 == 0)
{
lean_object* x_109; uint8_t x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_105, 0);
lean_dec(x_109);
x_110 = 1;
x_111 = lean_box(x_110);
lean_ctor_set(x_105, 0, x_111);
return x_104;
}
else
{
lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_105, 1);
lean_inc(x_112);
lean_dec(x_105);
x_113 = 1;
x_114 = lean_box(x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_112);
lean_ctor_set(x_104, 0, x_115);
return x_104;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_116 = lean_ctor_get(x_104, 1);
lean_inc(x_116);
lean_dec(x_104);
x_117 = lean_ctor_get(x_105, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_118 = x_105;
} else {
 lean_dec_ref(x_105);
 x_118 = lean_box(0);
}
x_119 = 1;
x_120 = lean_box(x_119);
if (lean_is_scalar(x_118)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_118;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_117);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_116);
return x_122;
}
}
else
{
uint8_t x_123; 
x_123 = !lean_is_exclusive(x_104);
if (x_123 == 0)
{
lean_object* x_124; uint8_t x_125; 
x_124 = lean_ctor_get(x_104, 0);
lean_dec(x_124);
x_125 = !lean_is_exclusive(x_105);
if (x_125 == 0)
{
return x_104;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_105, 0);
x_127 = lean_ctor_get(x_105, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_105);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
lean_ctor_set(x_104, 0, x_128);
return x_104;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_129 = lean_ctor_get(x_104, 1);
lean_inc(x_129);
lean_dec(x_104);
x_130 = lean_ctor_get(x_105, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_105, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_132 = x_105;
} else {
 lean_dec_ref(x_105);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(1, 2, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_131);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_129);
return x_134;
}
}
}
else
{
uint8_t x_135; 
x_135 = !lean_is_exclusive(x_104);
if (x_135 == 0)
{
return x_104;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_104, 0);
x_137 = lean_ctor_get(x_104, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_104);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_139 = lean_ctor_get(x_83, 1);
lean_inc(x_139);
lean_dec(x_83);
x_140 = lean_array_get_size(x_75);
x_141 = lean_unsigned_to_nat(0u);
x_142 = lean_nat_dec_lt(x_141, x_140);
if (x_142 == 0)
{
uint8_t x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_140);
lean_dec(x_75);
lean_dec(x_9);
x_143 = 1;
x_144 = lean_box(x_143);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_139);
if (lean_is_scalar(x_79)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_79;
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_84);
return x_146;
}
else
{
uint8_t x_147; 
x_147 = lean_nat_dec_le(x_140, x_140);
if (x_147 == 0)
{
uint8_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_140);
lean_dec(x_75);
lean_dec(x_9);
x_148 = 1;
x_149 = lean_box(x_148);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_139);
if (lean_is_scalar(x_79)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_79;
}
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_84);
return x_151;
}
else
{
size_t x_152; size_t x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_79);
x_152 = 0;
x_153 = lean_usize_of_nat(x_140);
lean_dec(x_140);
x_154 = l_Lake_buildUnlessUpToDate_x3f___rarg___closed__2;
x_155 = l_Lake_buildUnlessUpToDate_x3f___rarg___closed__3;
x_156 = lean_box(0);
x_157 = l_Array_foldlMUnsafe_fold___rarg(x_154, x_155, x_75, x_152, x_153, x_156);
x_158 = lean_apply_3(x_157, x_9, x_139, x_84);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_161 = x_158;
} else {
 lean_dec_ref(x_158);
 x_161 = lean_box(0);
}
x_162 = lean_ctor_get(x_159, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_163 = x_159;
} else {
 lean_dec_ref(x_159);
 x_163 = lean_box(0);
}
x_164 = 1;
x_165 = lean_box(x_164);
if (lean_is_scalar(x_163)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_163;
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_162);
if (lean_is_scalar(x_161)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_161;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_160);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_168 = lean_ctor_get(x_158, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_169 = x_158;
} else {
 lean_dec_ref(x_158);
 x_169 = lean_box(0);
}
x_170 = lean_ctor_get(x_159, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_159, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_172 = x_159;
} else {
 lean_dec_ref(x_159);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
if (lean_is_scalar(x_169)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_169;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_168);
return x_174;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_175 = lean_ctor_get(x_158, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_158, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_177 = x_158;
} else {
 lean_dec_ref(x_158);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 2, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
}
}
}
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_248; 
x_202 = lean_ctor_get(x_77, 0);
x_203 = lean_ctor_get(x_77, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_77);
x_248 = lean_unbox(x_202);
lean_dec(x_202);
if (x_248 == 0)
{
lean_object* x_249; 
lean_dec(x_79);
lean_dec(x_75);
x_249 = l_Lake_buildUnlessUpToDate_x3f_go(x_4, x_5, x_6, x_7, x_9, x_203, x_78);
return x_249;
}
else
{
lean_object* x_250; uint8_t x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; 
lean_dec(x_6);
lean_dec(x_4);
x_250 = lean_ctor_get(x_203, 0);
lean_inc(x_250);
x_251 = lean_ctor_get_uint8(x_203, sizeof(void*)*1);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 x_252 = x_203;
} else {
 lean_dec_ref(x_203);
 x_252 = lean_box(0);
}
x_253 = l_Lake_instOrdJobAction;
x_254 = 1;
x_255 = lean_box(x_251);
x_256 = lean_box(x_254);
x_257 = l_instDecidableRelLe___rarg(x_253, x_255, x_256);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
if (lean_is_scalar(x_252)) {
 x_258 = lean_alloc_ctor(0, 1, 1);
} else {
 x_258 = x_252;
}
lean_ctor_set(x_258, 0, x_250);
lean_ctor_set_uint8(x_258, sizeof(void*)*1, x_251);
x_259 = lean_box(0);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_258);
x_204 = x_260;
x_205 = x_78;
goto block_247;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
if (lean_is_scalar(x_252)) {
 x_261 = lean_alloc_ctor(0, 1, 1);
} else {
 x_261 = x_252;
}
lean_ctor_set(x_261, 0, x_250);
lean_ctor_set_uint8(x_261, sizeof(void*)*1, x_254);
x_262 = lean_box(0);
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_261);
x_204 = x_263;
x_205 = x_78;
goto block_247;
}
}
block_247:
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_207 = x_204;
} else {
 lean_dec_ref(x_204);
 x_207 = lean_box(0);
}
x_208 = lean_array_get_size(x_75);
x_209 = lean_unsigned_to_nat(0u);
x_210 = lean_nat_dec_lt(x_209, x_208);
if (x_210 == 0)
{
uint8_t x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_208);
lean_dec(x_75);
lean_dec(x_9);
x_211 = 1;
x_212 = lean_box(x_211);
if (lean_is_scalar(x_207)) {
 x_213 = lean_alloc_ctor(0, 2, 0);
} else {
 x_213 = x_207;
}
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_206);
if (lean_is_scalar(x_79)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_79;
}
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_205);
return x_214;
}
else
{
uint8_t x_215; 
x_215 = lean_nat_dec_le(x_208, x_208);
if (x_215 == 0)
{
uint8_t x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_208);
lean_dec(x_75);
lean_dec(x_9);
x_216 = 1;
x_217 = lean_box(x_216);
if (lean_is_scalar(x_207)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_207;
}
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_206);
if (lean_is_scalar(x_79)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_79;
}
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_205);
return x_219;
}
else
{
size_t x_220; size_t x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_207);
lean_dec(x_79);
x_220 = 0;
x_221 = lean_usize_of_nat(x_208);
lean_dec(x_208);
x_222 = l_Lake_buildUnlessUpToDate_x3f___rarg___closed__2;
x_223 = l_Lake_buildUnlessUpToDate_x3f___rarg___closed__3;
x_224 = lean_box(0);
x_225 = l_Array_foldlMUnsafe_fold___rarg(x_222, x_223, x_75, x_220, x_221, x_224);
x_226 = lean_apply_3(x_225, x_9, x_206, x_205);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; 
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
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
x_230 = lean_ctor_get(x_227, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_231 = x_227;
} else {
 lean_dec_ref(x_227);
 x_231 = lean_box(0);
}
x_232 = 1;
x_233 = lean_box(x_232);
if (lean_is_scalar(x_231)) {
 x_234 = lean_alloc_ctor(0, 2, 0);
} else {
 x_234 = x_231;
}
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_230);
if (lean_is_scalar(x_229)) {
 x_235 = lean_alloc_ctor(0, 2, 0);
} else {
 x_235 = x_229;
}
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_228);
return x_235;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_236 = lean_ctor_get(x_226, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 x_237 = x_226;
} else {
 lean_dec_ref(x_226);
 x_237 = lean_box(0);
}
x_238 = lean_ctor_get(x_227, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_227, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_240 = x_227;
} else {
 lean_dec_ref(x_227);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_241 = lean_alloc_ctor(1, 2, 0);
} else {
 x_241 = x_240;
}
lean_ctor_set(x_241, 0, x_238);
lean_ctor_set(x_241, 1, x_239);
if (lean_is_scalar(x_237)) {
 x_242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_242 = x_237;
}
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_236);
return x_242;
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_243 = lean_ctor_get(x_226, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_226, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 x_245 = x_226;
} else {
 lean_dec_ref(x_226);
 x_245 = lean_box(0);
}
if (lean_is_scalar(x_245)) {
 x_246 = lean_alloc_ctor(1, 2, 0);
} else {
 x_246 = x_245;
}
lean_ctor_set(x_246, 0, x_243);
lean_ctor_set(x_246, 1, x_244);
return x_246;
}
}
}
}
}
}
else
{
uint8_t x_264; 
lean_dec(x_75);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
x_264 = !lean_is_exclusive(x_76);
if (x_264 == 0)
{
lean_object* x_265; uint8_t x_266; 
x_265 = lean_ctor_get(x_76, 0);
lean_dec(x_265);
x_266 = !lean_is_exclusive(x_77);
if (x_266 == 0)
{
return x_76;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_77, 0);
x_268 = lean_ctor_get(x_77, 1);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_77);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
lean_ctor_set(x_76, 0, x_269);
return x_76;
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_270 = lean_ctor_get(x_76, 1);
lean_inc(x_270);
lean_dec(x_76);
x_271 = lean_ctor_get(x_77, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_77, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_273 = x_77;
} else {
 lean_dec_ref(x_77);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(1, 2, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_271);
lean_ctor_set(x_274, 1, x_272);
x_275 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_270);
return x_275;
}
}
}
else
{
uint8_t x_276; 
lean_dec(x_75);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
x_276 = !lean_is_exclusive(x_76);
if (x_276 == 0)
{
return x_76;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_277 = lean_ctor_get(x_76, 0);
x_278 = lean_ctor_get(x_76, 1);
lean_inc(x_278);
lean_inc(x_277);
lean_dec(x_76);
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_277);
lean_ctor_set(x_279, 1, x_278);
return x_279;
}
}
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_280 = lean_ctor_get(x_14, 0);
lean_inc(x_280);
lean_dec(x_14);
x_281 = lean_ctor_get(x_12, 1);
lean_inc(x_281);
lean_dec(x_12);
x_282 = lean_ctor_get(x_280, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_280, 1);
lean_inc(x_283);
lean_dec(x_280);
x_284 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_284, 0, x_282);
lean_inc(x_4);
x_285 = l_Lake_checkHashUpToDate___rarg(x_1, x_2, x_3, x_4, x_284, x_8, x_9, x_281, x_13);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; 
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; uint8_t x_336; 
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_288 = x_285;
} else {
 lean_dec_ref(x_285);
 x_288 = lean_box(0);
}
x_289 = lean_ctor_get(x_286, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_286, 1);
lean_inc(x_290);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 x_291 = x_286;
} else {
 lean_dec_ref(x_286);
 x_291 = lean_box(0);
}
x_336 = lean_unbox(x_289);
lean_dec(x_289);
if (x_336 == 0)
{
lean_object* x_337; 
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_283);
x_337 = l_Lake_buildUnlessUpToDate_x3f_go(x_4, x_5, x_6, x_7, x_9, x_290, x_287);
return x_337;
}
else
{
lean_object* x_338; uint8_t x_339; lean_object* x_340; lean_object* x_341; uint8_t x_342; lean_object* x_343; lean_object* x_344; uint8_t x_345; 
lean_dec(x_6);
lean_dec(x_4);
x_338 = lean_ctor_get(x_290, 0);
lean_inc(x_338);
x_339 = lean_ctor_get_uint8(x_290, sizeof(void*)*1);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 x_340 = x_290;
} else {
 lean_dec_ref(x_290);
 x_340 = lean_box(0);
}
x_341 = l_Lake_instOrdJobAction;
x_342 = 1;
x_343 = lean_box(x_339);
x_344 = lean_box(x_342);
x_345 = l_instDecidableRelLe___rarg(x_341, x_343, x_344);
if (x_345 == 0)
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; 
if (lean_is_scalar(x_340)) {
 x_346 = lean_alloc_ctor(0, 1, 1);
} else {
 x_346 = x_340;
}
lean_ctor_set(x_346, 0, x_338);
lean_ctor_set_uint8(x_346, sizeof(void*)*1, x_339);
x_347 = lean_box(0);
if (lean_is_scalar(x_291)) {
 x_348 = lean_alloc_ctor(0, 2, 0);
} else {
 x_348 = x_291;
}
lean_ctor_set(x_348, 0, x_347);
lean_ctor_set(x_348, 1, x_346);
x_292 = x_348;
x_293 = x_287;
goto block_335;
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; 
if (lean_is_scalar(x_340)) {
 x_349 = lean_alloc_ctor(0, 1, 1);
} else {
 x_349 = x_340;
}
lean_ctor_set(x_349, 0, x_338);
lean_ctor_set_uint8(x_349, sizeof(void*)*1, x_342);
x_350 = lean_box(0);
if (lean_is_scalar(x_291)) {
 x_351 = lean_alloc_ctor(0, 2, 0);
} else {
 x_351 = x_291;
}
lean_ctor_set(x_351, 0, x_350);
lean_ctor_set(x_351, 1, x_349);
x_292 = x_351;
x_293 = x_287;
goto block_335;
}
}
block_335:
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; 
x_294 = lean_ctor_get(x_292, 1);
lean_inc(x_294);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 lean_ctor_release(x_292, 1);
 x_295 = x_292;
} else {
 lean_dec_ref(x_292);
 x_295 = lean_box(0);
}
x_296 = lean_array_get_size(x_283);
x_297 = lean_unsigned_to_nat(0u);
x_298 = lean_nat_dec_lt(x_297, x_296);
if (x_298 == 0)
{
uint8_t x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_296);
lean_dec(x_283);
lean_dec(x_9);
x_299 = 1;
x_300 = lean_box(x_299);
if (lean_is_scalar(x_295)) {
 x_301 = lean_alloc_ctor(0, 2, 0);
} else {
 x_301 = x_295;
}
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_294);
if (lean_is_scalar(x_288)) {
 x_302 = lean_alloc_ctor(0, 2, 0);
} else {
 x_302 = x_288;
}
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_293);
return x_302;
}
else
{
uint8_t x_303; 
x_303 = lean_nat_dec_le(x_296, x_296);
if (x_303 == 0)
{
uint8_t x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
lean_dec(x_296);
lean_dec(x_283);
lean_dec(x_9);
x_304 = 1;
x_305 = lean_box(x_304);
if (lean_is_scalar(x_295)) {
 x_306 = lean_alloc_ctor(0, 2, 0);
} else {
 x_306 = x_295;
}
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_294);
if (lean_is_scalar(x_288)) {
 x_307 = lean_alloc_ctor(0, 2, 0);
} else {
 x_307 = x_288;
}
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_293);
return x_307;
}
else
{
size_t x_308; size_t x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_295);
lean_dec(x_288);
x_308 = 0;
x_309 = lean_usize_of_nat(x_296);
lean_dec(x_296);
x_310 = l_Lake_buildUnlessUpToDate_x3f___rarg___closed__2;
x_311 = l_Lake_buildUnlessUpToDate_x3f___rarg___closed__3;
x_312 = lean_box(0);
x_313 = l_Array_foldlMUnsafe_fold___rarg(x_310, x_311, x_283, x_308, x_309, x_312);
x_314 = lean_apply_3(x_313, x_9, x_294, x_293);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; 
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
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
x_318 = lean_ctor_get(x_315, 1);
lean_inc(x_318);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 x_319 = x_315;
} else {
 lean_dec_ref(x_315);
 x_319 = lean_box(0);
}
x_320 = 1;
x_321 = lean_box(x_320);
if (lean_is_scalar(x_319)) {
 x_322 = lean_alloc_ctor(0, 2, 0);
} else {
 x_322 = x_319;
}
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_318);
if (lean_is_scalar(x_317)) {
 x_323 = lean_alloc_ctor(0, 2, 0);
} else {
 x_323 = x_317;
}
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_316);
return x_323;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_324 = lean_ctor_get(x_314, 1);
lean_inc(x_324);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 lean_ctor_release(x_314, 1);
 x_325 = x_314;
} else {
 lean_dec_ref(x_314);
 x_325 = lean_box(0);
}
x_326 = lean_ctor_get(x_315, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_315, 1);
lean_inc(x_327);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 x_328 = x_315;
} else {
 lean_dec_ref(x_315);
 x_328 = lean_box(0);
}
if (lean_is_scalar(x_328)) {
 x_329 = lean_alloc_ctor(1, 2, 0);
} else {
 x_329 = x_328;
}
lean_ctor_set(x_329, 0, x_326);
lean_ctor_set(x_329, 1, x_327);
if (lean_is_scalar(x_325)) {
 x_330 = lean_alloc_ctor(0, 2, 0);
} else {
 x_330 = x_325;
}
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_324);
return x_330;
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_331 = lean_ctor_get(x_314, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_314, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 lean_ctor_release(x_314, 1);
 x_333 = x_314;
} else {
 lean_dec_ref(x_314);
 x_333 = lean_box(0);
}
if (lean_is_scalar(x_333)) {
 x_334 = lean_alloc_ctor(1, 2, 0);
} else {
 x_334 = x_333;
}
lean_ctor_set(x_334, 0, x_331);
lean_ctor_set(x_334, 1, x_332);
return x_334;
}
}
}
}
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
lean_dec(x_283);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
x_352 = lean_ctor_get(x_285, 1);
lean_inc(x_352);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_353 = x_285;
} else {
 lean_dec_ref(x_285);
 x_353 = lean_box(0);
}
x_354 = lean_ctor_get(x_286, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_286, 1);
lean_inc(x_355);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 x_356 = x_286;
} else {
 lean_dec_ref(x_286);
 x_356 = lean_box(0);
}
if (lean_is_scalar(x_356)) {
 x_357 = lean_alloc_ctor(1, 2, 0);
} else {
 x_357 = x_356;
}
lean_ctor_set(x_357, 0, x_354);
lean_ctor_set(x_357, 1, x_355);
if (lean_is_scalar(x_353)) {
 x_358 = lean_alloc_ctor(0, 2, 0);
} else {
 x_358 = x_353;
}
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set(x_358, 1, x_352);
return x_358;
}
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
lean_dec(x_283);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
x_359 = lean_ctor_get(x_285, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_285, 1);
lean_inc(x_360);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_361 = x_285;
} else {
 lean_dec_ref(x_285);
 x_361 = lean_box(0);
}
if (lean_is_scalar(x_361)) {
 x_362 = lean_alloc_ctor(1, 2, 0);
} else {
 x_362 = x_361;
}
lean_ctor_set(x_362, 0, x_359);
lean_ctor_set(x_362, 1, x_360);
return x_362;
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
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_buildUnlessUpToDate_x3f___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
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
lean_dec(x_5);
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
lean_dec(x_5);
return x_13;
}
}
static lean_object* _init_l_Lake_cacheFileHash___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".hash", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_cacheFileHash(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_computeBinFileHash(x_1, x_2);
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
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_176; uint8_t x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_176 = lean_ctor_get(x_6, 0);
lean_inc(x_176);
x_177 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_178 = x_6;
} else {
 lean_dec_ref(x_6);
 x_178 = lean_box(0);
}
if (x_2 == 0)
{
lean_object* x_196; 
x_196 = l_Lake_computeBinFileHash(x_3, x_7);
if (lean_obj_tag(x_196) == 0)
{
uint8_t x_197; 
x_197 = !lean_is_exclusive(x_196);
if (x_197 == 0)
{
lean_object* x_198; 
x_198 = lean_ctor_get(x_196, 1);
lean_ctor_set(x_196, 1, x_176);
x_179 = x_196;
x_180 = x_198;
goto block_195;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_196, 0);
x_200 = lean_ctor_get(x_196, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_196);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_176);
x_179 = x_201;
x_180 = x_200;
goto block_195;
}
}
else
{
uint8_t x_202; 
x_202 = !lean_is_exclusive(x_196);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_203 = lean_ctor_get(x_196, 0);
x_204 = lean_ctor_get(x_196, 1);
x_205 = lean_io_error_to_string(x_203);
x_206 = 3;
x_207 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set_uint8(x_207, sizeof(void*)*1, x_206);
x_208 = lean_array_get_size(x_176);
x_209 = lean_array_push(x_176, x_207);
lean_ctor_set(x_196, 1, x_209);
lean_ctor_set(x_196, 0, x_208);
x_179 = x_196;
x_180 = x_204;
goto block_195;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_210 = lean_ctor_get(x_196, 0);
x_211 = lean_ctor_get(x_196, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_196);
x_212 = lean_io_error_to_string(x_210);
x_213 = 3;
x_214 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set_uint8(x_214, sizeof(void*)*1, x_213);
x_215 = lean_array_get_size(x_176);
x_216 = lean_array_push(x_176, x_214);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
x_179 = x_217;
x_180 = x_211;
goto block_195;
}
}
}
else
{
lean_object* x_218; 
x_218 = l_Lake_computeTextFileHash(x_3, x_7);
if (lean_obj_tag(x_218) == 0)
{
uint8_t x_219; 
x_219 = !lean_is_exclusive(x_218);
if (x_219 == 0)
{
lean_object* x_220; 
x_220 = lean_ctor_get(x_218, 1);
lean_ctor_set(x_218, 1, x_176);
x_179 = x_218;
x_180 = x_220;
goto block_195;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_218, 0);
x_222 = lean_ctor_get(x_218, 1);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_218);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set(x_223, 1, x_176);
x_179 = x_223;
x_180 = x_222;
goto block_195;
}
}
else
{
uint8_t x_224; 
x_224 = !lean_is_exclusive(x_218);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_225 = lean_ctor_get(x_218, 0);
x_226 = lean_ctor_get(x_218, 1);
x_227 = lean_io_error_to_string(x_225);
x_228 = 3;
x_229 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set_uint8(x_229, sizeof(void*)*1, x_228);
x_230 = lean_array_get_size(x_176);
x_231 = lean_array_push(x_176, x_229);
lean_ctor_set(x_218, 1, x_231);
lean_ctor_set(x_218, 0, x_230);
x_179 = x_218;
x_180 = x_226;
goto block_195;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_232 = lean_ctor_get(x_218, 0);
x_233 = lean_ctor_get(x_218, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_218);
x_234 = lean_io_error_to_string(x_232);
x_235 = 3;
x_236 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set_uint8(x_236, sizeof(void*)*1, x_235);
x_237 = lean_array_get_size(x_176);
x_238 = lean_array_push(x_176, x_236);
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
x_179 = x_239;
x_180 = x_233;
goto block_195;
}
}
}
block_175:
{
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_91; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 1);
x_91 = !lean_is_exclusive(x_12);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_12, 0);
x_93 = l_Lake_createParentDirs(x_1, x_9);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
lean_ctor_set(x_8, 0, x_94);
x_13 = x_8;
x_14 = x_95;
goto block_90;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_96 = lean_ctor_get(x_93, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_93, 1);
lean_inc(x_97);
lean_dec(x_93);
x_98 = lean_io_error_to_string(x_96);
x_99 = 3;
x_100 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set_uint8(x_100, sizeof(void*)*1, x_99);
x_101 = lean_array_get_size(x_92);
x_102 = lean_array_push(x_92, x_100);
lean_ctor_set(x_12, 0, x_102);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_101);
x_13 = x_8;
x_14 = x_97;
goto block_90;
}
}
else
{
lean_object* x_103; uint8_t x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_12, 0);
x_104 = lean_ctor_get_uint8(x_12, sizeof(void*)*1);
lean_inc(x_103);
lean_dec(x_12);
x_105 = l_Lake_createParentDirs(x_1, x_9);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_108, 0, x_103);
lean_ctor_set_uint8(x_108, sizeof(void*)*1, x_104);
lean_ctor_set(x_8, 1, x_108);
lean_ctor_set(x_8, 0, x_106);
x_13 = x_8;
x_14 = x_107;
goto block_90;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_109 = lean_ctor_get(x_105, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_105, 1);
lean_inc(x_110);
lean_dec(x_105);
x_111 = lean_io_error_to_string(x_109);
x_112 = 3;
x_113 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set_uint8(x_113, sizeof(void*)*1, x_112);
x_114 = lean_array_get_size(x_103);
x_115 = lean_array_push(x_103, x_113);
x_116 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set_uint8(x_116, sizeof(void*)*1, x_104);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 1, x_116);
lean_ctor_set(x_8, 0, x_114);
x_13 = x_8;
x_14 = x_110;
goto block_90;
}
}
block_90:
{
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint64_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = lean_unbox_uint64(x_11);
x_19 = lean_uint64_to_nat(x_18);
x_20 = l___private_Init_Data_Repr_0__Nat_reprFast(x_19);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = l_IO_FS_writeFile(x_1, x_20, x_14);
lean_dec(x_20);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_23, 0, x_13);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
lean_ctor_set(x_13, 0, x_11);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_13);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_11);
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_23, 0);
x_30 = lean_io_error_to_string(x_29);
x_31 = 3;
x_32 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_31);
x_33 = lean_array_get_size(x_22);
x_34 = lean_array_push(x_22, x_32);
lean_ctor_set(x_16, 0, x_34);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_33);
lean_ctor_set_tag(x_23, 0);
lean_ctor_set(x_23, 0, x_13);
return x_23;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_23, 0);
x_36 = lean_ctor_get(x_23, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_23);
x_37 = lean_io_error_to_string(x_35);
x_38 = 3;
x_39 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_38);
x_40 = lean_array_get_size(x_22);
x_41 = lean_array_push(x_22, x_39);
lean_ctor_set(x_16, 0, x_41);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_13);
lean_ctor_set(x_42, 1, x_36);
return x_42;
}
}
}
else
{
lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_16, 0);
x_44 = lean_ctor_get_uint8(x_16, sizeof(void*)*1);
lean_inc(x_43);
lean_dec(x_16);
x_45 = l_IO_FS_writeFile(x_1, x_20, x_14);
lean_dec(x_20);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
x_48 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_44);
lean_ctor_set(x_13, 1, x_48);
lean_ctor_set(x_13, 0, x_11);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_13);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_11);
x_50 = lean_ctor_get(x_45, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_45, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_52 = x_45;
} else {
 lean_dec_ref(x_45);
 x_52 = lean_box(0);
}
x_53 = lean_io_error_to_string(x_50);
x_54 = 3;
x_55 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_54);
x_56 = lean_array_get_size(x_43);
x_57 = lean_array_push(x_43, x_55);
x_58 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_44);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 1, x_58);
lean_ctor_set(x_13, 0, x_56);
if (lean_is_scalar(x_52)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_52;
 lean_ctor_set_tag(x_59, 0);
}
lean_ctor_set(x_59, 0, x_13);
lean_ctor_set(x_59, 1, x_51);
return x_59;
}
}
}
else
{
lean_object* x_60; uint64_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; 
x_60 = lean_ctor_get(x_13, 1);
lean_inc(x_60);
lean_dec(x_13);
x_61 = lean_unbox_uint64(x_11);
x_62 = lean_uint64_to_nat(x_61);
x_63 = l___private_Init_Data_Repr_0__Nat_reprFast(x_62);
x_64 = lean_ctor_get(x_60, 0);
lean_inc(x_64);
x_65 = lean_ctor_get_uint8(x_60, sizeof(void*)*1);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 x_66 = x_60;
} else {
 lean_dec_ref(x_60);
 x_66 = lean_box(0);
}
x_67 = l_IO_FS_writeFile(x_1, x_63, x_14);
lean_dec(x_63);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_70 = lean_alloc_ctor(0, 1, 1);
} else {
 x_70 = x_66;
}
lean_ctor_set(x_70, 0, x_64);
lean_ctor_set_uint8(x_70, sizeof(void*)*1, x_65);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_11);
lean_ctor_set(x_71, 1, x_70);
if (lean_is_scalar(x_69)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_69;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_68);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_11);
x_73 = lean_ctor_get(x_67, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_67, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_75 = x_67;
} else {
 lean_dec_ref(x_67);
 x_75 = lean_box(0);
}
x_76 = lean_io_error_to_string(x_73);
x_77 = 3;
x_78 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set_uint8(x_78, sizeof(void*)*1, x_77);
x_79 = lean_array_get_size(x_64);
x_80 = lean_array_push(x_64, x_78);
if (lean_is_scalar(x_66)) {
 x_81 = lean_alloc_ctor(0, 1, 1);
} else {
 x_81 = x_66;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set_uint8(x_81, sizeof(void*)*1, x_65);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_81);
if (lean_is_scalar(x_75)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_75;
 lean_ctor_set_tag(x_83, 0);
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_74);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_11);
x_84 = !lean_is_exclusive(x_13);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_13);
lean_ctor_set(x_85, 1, x_14);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_13, 0);
x_87 = lean_ctor_get(x_13, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_13);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_14);
return x_89;
}
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_152; uint8_t x_153; lean_object* x_154; lean_object* x_155; 
x_117 = lean_ctor_get(x_8, 0);
x_118 = lean_ctor_get(x_8, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_8);
x_152 = lean_ctor_get(x_118, 0);
lean_inc(x_152);
x_153 = lean_ctor_get_uint8(x_118, sizeof(void*)*1);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 x_154 = x_118;
} else {
 lean_dec_ref(x_118);
 x_154 = lean_box(0);
}
x_155 = l_Lake_createParentDirs(x_1, x_9);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
if (lean_is_scalar(x_154)) {
 x_158 = lean_alloc_ctor(0, 1, 1);
} else {
 x_158 = x_154;
}
lean_ctor_set(x_158, 0, x_152);
lean_ctor_set_uint8(x_158, sizeof(void*)*1, x_153);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_158);
x_119 = x_159;
x_120 = x_157;
goto block_151;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_160 = lean_ctor_get(x_155, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_155, 1);
lean_inc(x_161);
lean_dec(x_155);
x_162 = lean_io_error_to_string(x_160);
x_163 = 3;
x_164 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set_uint8(x_164, sizeof(void*)*1, x_163);
x_165 = lean_array_get_size(x_152);
x_166 = lean_array_push(x_152, x_164);
if (lean_is_scalar(x_154)) {
 x_167 = lean_alloc_ctor(0, 1, 1);
} else {
 x_167 = x_154;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set_uint8(x_167, sizeof(void*)*1, x_153);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_167);
x_119 = x_168;
x_120 = x_161;
goto block_151;
}
block_151:
{
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_121; lean_object* x_122; uint64_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; 
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_122 = x_119;
} else {
 lean_dec_ref(x_119);
 x_122 = lean_box(0);
}
x_123 = lean_unbox_uint64(x_117);
x_124 = lean_uint64_to_nat(x_123);
x_125 = l___private_Init_Data_Repr_0__Nat_reprFast(x_124);
x_126 = lean_ctor_get(x_121, 0);
lean_inc(x_126);
x_127 = lean_ctor_get_uint8(x_121, sizeof(void*)*1);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 x_128 = x_121;
} else {
 lean_dec_ref(x_121);
 x_128 = lean_box(0);
}
x_129 = l_IO_FS_writeFile(x_1, x_125, x_120);
lean_dec(x_125);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_131 = x_129;
} else {
 lean_dec_ref(x_129);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_132 = lean_alloc_ctor(0, 1, 1);
} else {
 x_132 = x_128;
}
lean_ctor_set(x_132, 0, x_126);
lean_ctor_set_uint8(x_132, sizeof(void*)*1, x_127);
if (lean_is_scalar(x_122)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_122;
}
lean_ctor_set(x_133, 0, x_117);
lean_ctor_set(x_133, 1, x_132);
if (lean_is_scalar(x_131)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_131;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_130);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_117);
x_135 = lean_ctor_get(x_129, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_129, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_137 = x_129;
} else {
 lean_dec_ref(x_129);
 x_137 = lean_box(0);
}
x_138 = lean_io_error_to_string(x_135);
x_139 = 3;
x_140 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set_uint8(x_140, sizeof(void*)*1, x_139);
x_141 = lean_array_get_size(x_126);
x_142 = lean_array_push(x_126, x_140);
if (lean_is_scalar(x_128)) {
 x_143 = lean_alloc_ctor(0, 1, 1);
} else {
 x_143 = x_128;
}
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set_uint8(x_143, sizeof(void*)*1, x_127);
if (lean_is_scalar(x_122)) {
 x_144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_144 = x_122;
 lean_ctor_set_tag(x_144, 1);
}
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_143);
if (lean_is_scalar(x_137)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_137;
 lean_ctor_set_tag(x_145, 0);
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_136);
return x_145;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_117);
x_146 = lean_ctor_get(x_119, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_119, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_148 = x_119;
} else {
 lean_dec_ref(x_119);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_120);
return x_150;
}
}
}
}
else
{
uint8_t x_169; 
x_169 = !lean_is_exclusive(x_8);
if (x_169 == 0)
{
lean_object* x_170; 
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_8);
lean_ctor_set(x_170, 1, x_9);
return x_170;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_171 = lean_ctor_get(x_8, 0);
x_172 = lean_ctor_get(x_8, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_8);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_9);
return x_174;
}
}
}
block_195:
{
if (lean_obj_tag(x_179) == 0)
{
uint8_t x_181; 
x_181 = !lean_is_exclusive(x_179);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_179, 1);
if (lean_is_scalar(x_178)) {
 x_183 = lean_alloc_ctor(0, 1, 1);
} else {
 x_183 = x_178;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set_uint8(x_183, sizeof(void*)*1, x_177);
lean_ctor_set(x_179, 1, x_183);
x_8 = x_179;
x_9 = x_180;
goto block_175;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_ctor_get(x_179, 0);
x_185 = lean_ctor_get(x_179, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_179);
if (lean_is_scalar(x_178)) {
 x_186 = lean_alloc_ctor(0, 1, 1);
} else {
 x_186 = x_178;
}
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set_uint8(x_186, sizeof(void*)*1, x_177);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_186);
x_8 = x_187;
x_9 = x_180;
goto block_175;
}
}
else
{
uint8_t x_188; 
x_188 = !lean_is_exclusive(x_179);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_179, 1);
if (lean_is_scalar(x_178)) {
 x_190 = lean_alloc_ctor(0, 1, 1);
} else {
 x_190 = x_178;
}
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set_uint8(x_190, sizeof(void*)*1, x_177);
lean_ctor_set(x_179, 1, x_190);
x_8 = x_179;
x_9 = x_180;
goto block_175;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_191 = lean_ctor_get(x_179, 0);
x_192 = lean_ctor_get(x_179, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_179);
if (lean_is_scalar(x_178)) {
 x_193 = lean_alloc_ctor(0, 1, 1);
} else {
 x_193 = x_178;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set_uint8(x_193, sizeof(void*)*1, x_177);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_193);
x_8 = x_194;
x_9 = x_180;
goto block_175;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = l_Lake_cacheFileHash___closed__1;
lean_inc(x_1);
x_7 = lean_string_append(x_1, x_6);
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lake_fetchFileHash___lambda__1(x_7, x_2, x_1, x_10, x_3, x_4, x_5);
lean_dec(x_1);
lean_dec(x_7);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lake_Hash_load_x3f(x_7, x_5);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 1);
lean_free_object(x_13);
x_17 = lean_box(0);
x_18 = l_Lake_fetchFileHash___lambda__1(x_7, x_2, x_1, x_17, x_3, x_4, x_16);
lean_dec(x_1);
lean_dec(x_7);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
lean_dec(x_1);
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_4);
lean_ctor_set(x_13, 0, x_20);
return x_13;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = l_Lake_fetchFileHash___lambda__1(x_7, x_2, x_1, x_23, x_3, x_4, x_22);
lean_dec(x_1);
lean_dec(x_7);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_7);
lean_dec(x_1);
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_4);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
return x_27;
}
}
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_4, 0);
x_29 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_inc(x_28);
lean_dec(x_4);
x_30 = l_Lake_Hash_load_x3f(x_7, x_5);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_33);
x_35 = lean_box(0);
x_36 = l_Lake_fetchFileHash___lambda__1(x_7, x_2, x_1, x_35, x_3, x_34, x_32);
lean_dec(x_1);
lean_dec(x_7);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_7);
lean_dec(x_1);
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
if (lean_is_scalar(x_33)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_33;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_32);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lake_fetchFileHash___lambda__1(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileHash___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lake_fetchFileHash(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_6 = l_Lake_fetchFileHash(x_1, x_2, x_3, x_4, x_5);
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
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_io_metadata(x_1, x_9);
lean_dec(x_1);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_7, 0, x_19);
lean_ctor_set(x_15, 0, x_7);
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
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_11);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_7, 0, x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_7);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_11);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_io_error_to_string(x_26);
x_28 = 3;
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
x_30 = lean_array_get_size(x_14);
x_31 = lean_array_push(x_14, x_29);
lean_ctor_set(x_8, 0, x_31);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_30);
lean_ctor_set_tag(x_15, 0);
lean_ctor_set(x_15, 0, x_7);
return x_15;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_15, 0);
x_33 = lean_ctor_get(x_15, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_15);
x_34 = lean_io_error_to_string(x_32);
x_35 = 3;
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_35);
x_37 = lean_array_get_size(x_14);
x_38 = lean_array_push(x_14, x_36);
lean_ctor_set(x_8, 0, x_38);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_7);
lean_ctor_set(x_39, 1, x_33);
return x_39;
}
}
}
else
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_8, 0);
x_41 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
lean_inc(x_40);
lean_dec(x_8);
x_42 = lean_io_metadata(x_1, x_9);
lean_dec(x_1);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
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
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_47, 0, x_40);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_41);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_11);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set(x_7, 1, x_47);
lean_ctor_set(x_7, 0, x_48);
if (lean_is_scalar(x_45)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_45;
}
lean_ctor_set(x_49, 0, x_7);
lean_ctor_set(x_49, 1, x_44);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_11);
x_50 = lean_ctor_get(x_42, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_42, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_52 = x_42;
} else {
 lean_dec_ref(x_42);
 x_52 = lean_box(0);
}
x_53 = lean_io_error_to_string(x_50);
x_54 = 3;
x_55 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_54);
x_56 = lean_array_get_size(x_40);
x_57 = lean_array_push(x_40, x_55);
x_58 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_41);
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
lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_7, 0);
lean_inc(x_60);
lean_dec(x_7);
x_61 = lean_ctor_get(x_8, 0);
lean_inc(x_61);
x_62 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_63 = x_8;
} else {
 lean_dec_ref(x_8);
 x_63 = lean_box(0);
}
x_64 = lean_io_metadata(x_1, x_9);
lean_dec(x_1);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
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
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
if (lean_is_scalar(x_63)) {
 x_69 = lean_alloc_ctor(0, 1, 1);
} else {
 x_69 = x_63;
}
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set_uint8(x_69, sizeof(void*)*1, x_62);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_60);
lean_ctor_set(x_70, 1, x_68);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
if (lean_is_scalar(x_67)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_67;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_66);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_60);
x_73 = lean_ctor_get(x_64, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_64, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_75 = x_64;
} else {
 lean_dec_ref(x_64);
 x_75 = lean_box(0);
}
x_76 = lean_io_error_to_string(x_73);
x_77 = 3;
x_78 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set_uint8(x_78, sizeof(void*)*1, x_77);
x_79 = lean_array_get_size(x_61);
x_80 = lean_array_push(x_61, x_78);
if (lean_is_scalar(x_63)) {
 x_81 = lean_alloc_ctor(0, 1, 1);
} else {
 x_81 = x_63;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set_uint8(x_81, sizeof(void*)*1, x_62);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_81);
if (lean_is_scalar(x_75)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_75;
 lean_ctor_set_tag(x_83, 0);
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_74);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_6);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_ctor_get(x_6, 0);
lean_dec(x_85);
x_86 = !lean_is_exclusive(x_7);
if (x_86 == 0)
{
return x_6;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_7, 0);
x_88 = lean_ctor_get(x_7, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_7);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_6, 0, x_89);
return x_6;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_90 = lean_ctor_get(x_6, 1);
lean_inc(x_90);
lean_dec(x_6);
x_91 = lean_ctor_get(x_7, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_7, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_93 = x_7;
} else {
 lean_dec_ref(x_7);
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
return x_95;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_fetchFileTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lake_fetchFileTrace(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_3);
return x_7;
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
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_buildFileUnlessUpToDate___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_277; 
x_11 = lean_alloc_closure((void*)(l_Lake_buildUnlessUpToDate_x3f___at_Lake_buildFileUnlessUpToDate___spec__2___lambda__1___boxed), 5, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_11);
x_277 = !lean_is_exclusive(x_9);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; 
x_278 = lean_ctor_get(x_9, 0);
x_279 = l_System_FilePath_pathExists(x_5, x_10);
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_unbox(x_280);
lean_dec(x_280);
if (x_281 == 0)
{
uint8_t x_282; 
lean_dec(x_7);
x_282 = !lean_is_exclusive(x_279);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_283 = lean_ctor_get(x_279, 1);
x_284 = lean_ctor_get(x_279, 0);
lean_dec(x_284);
x_285 = lean_ctor_get(x_4, 1);
lean_inc(x_285);
x_286 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__3(x_3, x_285, x_283);
x_287 = !lean_is_exclusive(x_286);
if (x_287 == 0)
{
lean_object* x_288; lean_object* x_289; uint8_t x_290; 
x_288 = lean_ctor_get(x_286, 0);
x_289 = lean_ctor_get(x_286, 1);
x_290 = lean_unbox(x_288);
lean_dec(x_288);
if (x_290 == 0)
{
lean_object* x_291; 
lean_free_object(x_286);
lean_free_object(x_279);
x_291 = l_Lake_buildUnlessUpToDate_x3f_go(x_4, x_5, x_12, x_6, x_8, x_9, x_289);
return x_291;
}
else
{
uint8_t x_292; lean_object* x_293; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_4);
x_292 = 1;
x_293 = lean_box(x_292);
lean_ctor_set(x_279, 1, x_9);
lean_ctor_set(x_279, 0, x_293);
lean_ctor_set(x_286, 0, x_279);
return x_286;
}
}
else
{
lean_object* x_294; lean_object* x_295; uint8_t x_296; 
x_294 = lean_ctor_get(x_286, 0);
x_295 = lean_ctor_get(x_286, 1);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_286);
x_296 = lean_unbox(x_294);
lean_dec(x_294);
if (x_296 == 0)
{
lean_object* x_297; 
lean_free_object(x_279);
x_297 = l_Lake_buildUnlessUpToDate_x3f_go(x_4, x_5, x_12, x_6, x_8, x_9, x_295);
return x_297;
}
else
{
uint8_t x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_4);
x_298 = 1;
x_299 = lean_box(x_298);
lean_ctor_set(x_279, 1, x_9);
lean_ctor_set(x_279, 0, x_299);
x_300 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_300, 0, x_279);
lean_ctor_set(x_300, 1, x_295);
return x_300;
}
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; 
x_301 = lean_ctor_get(x_279, 1);
lean_inc(x_301);
lean_dec(x_279);
x_302 = lean_ctor_get(x_4, 1);
lean_inc(x_302);
x_303 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__3(x_3, x_302, x_301);
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
x_307 = lean_unbox(x_304);
lean_dec(x_304);
if (x_307 == 0)
{
lean_object* x_308; 
lean_dec(x_306);
x_308 = l_Lake_buildUnlessUpToDate_x3f_go(x_4, x_5, x_12, x_6, x_8, x_9, x_305);
return x_308;
}
else
{
uint8_t x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_4);
x_309 = 1;
x_310 = lean_box(x_309);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_9);
if (lean_is_scalar(x_306)) {
 x_312 = lean_alloc_ctor(0, 2, 0);
} else {
 x_312 = x_306;
}
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_312, 1, x_305);
return x_312;
}
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; 
x_313 = lean_ctor_get(x_279, 1);
lean_inc(x_313);
lean_dec(x_279);
x_314 = l_Lake_readTraceFile_x3f(x_5, x_278, x_313);
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
lean_dec(x_314);
x_317 = !lean_is_exclusive(x_315);
if (x_317 == 0)
{
lean_object* x_318; 
x_318 = lean_ctor_get(x_315, 1);
lean_ctor_set(x_9, 0, x_318);
lean_ctor_set(x_315, 1, x_9);
x_13 = x_315;
x_14 = x_316;
goto block_276;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_319 = lean_ctor_get(x_315, 0);
x_320 = lean_ctor_get(x_315, 1);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_315);
lean_ctor_set(x_9, 0, x_320);
x_321 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_321, 0, x_319);
lean_ctor_set(x_321, 1, x_9);
x_13 = x_321;
x_14 = x_316;
goto block_276;
}
}
}
else
{
lean_object* x_322; uint8_t x_323; lean_object* x_324; lean_object* x_325; uint8_t x_326; 
x_322 = lean_ctor_get(x_9, 0);
x_323 = lean_ctor_get_uint8(x_9, sizeof(void*)*1);
lean_inc(x_322);
lean_dec(x_9);
x_324 = l_System_FilePath_pathExists(x_5, x_10);
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
x_326 = lean_unbox(x_325);
lean_dec(x_325);
if (x_326 == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; 
lean_dec(x_7);
x_327 = lean_ctor_get(x_324, 1);
lean_inc(x_327);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 lean_ctor_release(x_324, 1);
 x_328 = x_324;
} else {
 lean_dec_ref(x_324);
 x_328 = lean_box(0);
}
x_329 = lean_ctor_get(x_4, 1);
lean_inc(x_329);
x_330 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__3(x_3, x_329, x_327);
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_330, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 x_333 = x_330;
} else {
 lean_dec_ref(x_330);
 x_333 = lean_box(0);
}
x_334 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_334, 0, x_322);
lean_ctor_set_uint8(x_334, sizeof(void*)*1, x_323);
x_335 = lean_unbox(x_331);
lean_dec(x_331);
if (x_335 == 0)
{
lean_object* x_336; 
lean_dec(x_333);
lean_dec(x_328);
x_336 = l_Lake_buildUnlessUpToDate_x3f_go(x_4, x_5, x_12, x_6, x_8, x_334, x_332);
return x_336;
}
else
{
uint8_t x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_4);
x_337 = 1;
x_338 = lean_box(x_337);
if (lean_is_scalar(x_328)) {
 x_339 = lean_alloc_ctor(0, 2, 0);
} else {
 x_339 = x_328;
}
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_334);
if (lean_is_scalar(x_333)) {
 x_340 = lean_alloc_ctor(0, 2, 0);
} else {
 x_340 = x_333;
}
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_332);
return x_340;
}
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_341 = lean_ctor_get(x_324, 1);
lean_inc(x_341);
lean_dec(x_324);
x_342 = l_Lake_readTraceFile_x3f(x_5, x_322, x_341);
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
lean_ctor_set_uint8(x_348, sizeof(void*)*1, x_323);
if (lean_is_scalar(x_347)) {
 x_349 = lean_alloc_ctor(0, 2, 0);
} else {
 x_349 = x_347;
}
lean_ctor_set(x_349, 0, x_345);
lean_ctor_set(x_349, 1, x_348);
x_13 = x_349;
x_14 = x_344;
goto block_276;
}
}
block_276:
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
x_19 = lean_ctor_get(x_8, 0);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_19, sizeof(void*)*1);
lean_dec(x_19);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__3(x_3, x_7, x_14);
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
x_26 = l_Lake_buildUnlessUpToDate_x3f_go(x_4, x_5, x_12, x_6, x_8, x_17, x_25);
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
x_30 = l_Lake_buildUnlessUpToDate_x3f_go(x_4, x_5, x_12, x_6, x_8, x_17, x_28);
return x_30;
}
else
{
uint8_t x_31; lean_object* x_32; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_4);
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
x_35 = l_Lake_buildUnlessUpToDate_x3f_go(x_4, x_5, x_12, x_6, x_8, x_17, x_34);
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
x_37 = l_Lake_buildUnlessUpToDate_x3f_go(x_4, x_5, x_12, x_6, x_8, x_17, x_34);
return x_37;
}
else
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_4);
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
lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_17, 0);
x_42 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
lean_inc(x_41);
lean_dec(x_17);
x_43 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__3(x_3, x_7, x_14);
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
x_47 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_47, 0, x_41);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_42);
if (x_20 == 0)
{
lean_object* x_48; 
lean_dec(x_46);
lean_dec(x_44);
lean_free_object(x_13);
x_48 = l_Lake_buildUnlessUpToDate_x3f_go(x_4, x_5, x_12, x_6, x_8, x_47, x_45);
return x_48;
}
else
{
uint8_t x_49; 
x_49 = lean_unbox(x_44);
lean_dec(x_44);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_46);
lean_free_object(x_13);
x_50 = l_Lake_buildUnlessUpToDate_x3f_go(x_4, x_5, x_12, x_6, x_8, x_47, x_45);
return x_50;
}
else
{
uint8_t x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_4);
x_51 = 1;
x_52 = lean_box(x_51);
lean_ctor_set(x_13, 1, x_47);
lean_ctor_set(x_13, 0, x_52);
if (lean_is_scalar(x_46)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_46;
}
lean_ctor_set(x_53, 0, x_13);
lean_ctor_set(x_53, 1, x_45);
return x_53;
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_54 = lean_ctor_get(x_13, 1);
lean_inc(x_54);
lean_dec(x_13);
x_55 = lean_ctor_get(x_8, 0);
lean_inc(x_55);
x_56 = lean_ctor_get_uint8(x_55, sizeof(void*)*1);
lean_dec(x_55);
x_57 = lean_ctor_get(x_54, 0);
lean_inc(x_57);
x_58 = lean_ctor_get_uint8(x_54, sizeof(void*)*1);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 x_59 = x_54;
} else {
 lean_dec_ref(x_54);
 x_59 = lean_box(0);
}
x_60 = l_Lake_MTime_checkUpToDate___at_Lake_buildFileUnlessUpToDate___spec__3(x_3, x_7, x_14);
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
if (x_56 == 0)
{
lean_object* x_65; 
lean_dec(x_63);
lean_dec(x_61);
x_65 = l_Lake_buildUnlessUpToDate_x3f_go(x_4, x_5, x_12, x_6, x_8, x_64, x_62);
return x_65;
}
else
{
uint8_t x_66; 
x_66 = lean_unbox(x_61);
lean_dec(x_61);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_63);
x_67 = l_Lake_buildUnlessUpToDate_x3f_go(x_4, x_5, x_12, x_6, x_8, x_64, x_62);
return x_67;
}
else
{
uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_4);
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
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_15);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_73 = lean_ctor_get(x_15, 0);
x_74 = lean_ctor_get(x_13, 1);
lean_inc(x_74);
lean_dec(x_13);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
lean_ctor_set(x_15, 0, x_75);
lean_inc(x_4);
x_77 = l_Lake_checkHashUpToDate___at_Lake_buildFileUnlessUpToDate___spec__4(x_3, x_4, x_15, x_7, x_8, x_74, x_14);
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
x_81 = !lean_is_exclusive(x_78);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_148; 
x_82 = lean_ctor_get(x_78, 0);
x_83 = lean_ctor_get(x_78, 1);
x_148 = lean_unbox(x_82);
lean_dec(x_82);
if (x_148 == 0)
{
lean_object* x_149; 
lean_free_object(x_78);
lean_dec(x_80);
lean_dec(x_76);
x_149 = l_Lake_buildUnlessUpToDate_x3f_go(x_4, x_5, x_12, x_6, x_8, x_83, x_79);
return x_149;
}
else
{
uint8_t x_150; 
lean_dec(x_12);
lean_dec(x_4);
x_150 = !lean_is_exclusive(x_83);
if (x_150 == 0)
{
uint8_t x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_151 = lean_ctor_get_uint8(x_83, sizeof(void*)*1);
x_152 = l_Lake_instOrdJobAction;
x_153 = 1;
x_154 = lean_box(x_151);
x_155 = lean_box(x_153);
x_156 = l_instDecidableRelLe___rarg(x_152, x_154, x_155);
if (x_156 == 0)
{
lean_object* x_157; 
x_157 = lean_box(0);
lean_ctor_set(x_78, 0, x_157);
x_84 = x_78;
x_85 = x_79;
goto block_147;
}
else
{
lean_object* x_158; 
lean_ctor_set_uint8(x_83, sizeof(void*)*1, x_153);
x_158 = lean_box(0);
lean_ctor_set(x_78, 0, x_158);
x_84 = x_78;
x_85 = x_79;
goto block_147;
}
}
else
{
lean_object* x_159; uint8_t x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_159 = lean_ctor_get(x_83, 0);
x_160 = lean_ctor_get_uint8(x_83, sizeof(void*)*1);
lean_inc(x_159);
lean_dec(x_83);
x_161 = l_Lake_instOrdJobAction;
x_162 = 1;
x_163 = lean_box(x_160);
x_164 = lean_box(x_162);
x_165 = l_instDecidableRelLe___rarg(x_161, x_163, x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_166, 0, x_159);
lean_ctor_set_uint8(x_166, sizeof(void*)*1, x_160);
x_167 = lean_box(0);
lean_ctor_set(x_78, 1, x_166);
lean_ctor_set(x_78, 0, x_167);
x_84 = x_78;
x_85 = x_79;
goto block_147;
}
else
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_168, 0, x_159);
lean_ctor_set_uint8(x_168, sizeof(void*)*1, x_162);
x_169 = lean_box(0);
lean_ctor_set(x_78, 1, x_168);
lean_ctor_set(x_78, 0, x_169);
x_84 = x_78;
x_85 = x_79;
goto block_147;
}
}
}
block_147:
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_84);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_87 = lean_ctor_get(x_84, 1);
x_88 = lean_ctor_get(x_84, 0);
lean_dec(x_88);
x_89 = lean_array_get_size(x_76);
x_90 = lean_unsigned_to_nat(0u);
x_91 = lean_nat_dec_lt(x_90, x_89);
if (x_91 == 0)
{
uint8_t x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_89);
lean_dec(x_76);
lean_dec(x_8);
x_92 = 1;
x_93 = lean_box(x_92);
lean_ctor_set(x_84, 0, x_93);
if (lean_is_scalar(x_80)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_80;
}
lean_ctor_set(x_94, 0, x_84);
lean_ctor_set(x_94, 1, x_85);
return x_94;
}
else
{
uint8_t x_95; 
x_95 = lean_nat_dec_le(x_89, x_89);
if (x_95 == 0)
{
uint8_t x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_89);
lean_dec(x_76);
lean_dec(x_8);
x_96 = 1;
x_97 = lean_box(x_96);
lean_ctor_set(x_84, 0, x_97);
if (lean_is_scalar(x_80)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_80;
}
lean_ctor_set(x_98, 0, x_84);
lean_ctor_set(x_98, 1, x_85);
return x_98;
}
else
{
size_t x_99; size_t x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
lean_free_object(x_84);
lean_dec(x_80);
x_99 = 0;
x_100 = lean_usize_of_nat(x_89);
lean_dec(x_89);
x_101 = lean_box(0);
x_102 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate___spec__6(x_76, x_99, x_100, x_101, x_8, x_87, x_85);
lean_dec(x_8);
lean_dec(x_76);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_ctor_get(x_102, 0);
x_105 = !lean_is_exclusive(x_104);
if (x_105 == 0)
{
lean_object* x_106; uint8_t x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_104, 0);
lean_dec(x_106);
x_107 = 1;
x_108 = lean_box(x_107);
lean_ctor_set(x_104, 0, x_108);
return x_102;
}
else
{
lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_104, 1);
lean_inc(x_109);
lean_dec(x_104);
x_110 = 1;
x_111 = lean_box(x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_109);
lean_ctor_set(x_102, 0, x_112);
return x_102;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_113 = lean_ctor_get(x_102, 0);
x_114 = lean_ctor_get(x_102, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_102);
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
x_117 = 1;
x_118 = lean_box(x_117);
if (lean_is_scalar(x_116)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_116;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_115);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_114);
return x_120;
}
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_121 = lean_ctor_get(x_84, 1);
lean_inc(x_121);
lean_dec(x_84);
x_122 = lean_array_get_size(x_76);
x_123 = lean_unsigned_to_nat(0u);
x_124 = lean_nat_dec_lt(x_123, x_122);
if (x_124 == 0)
{
uint8_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_122);
lean_dec(x_76);
lean_dec(x_8);
x_125 = 1;
x_126 = lean_box(x_125);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_121);
if (lean_is_scalar(x_80)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_80;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_85);
return x_128;
}
else
{
uint8_t x_129; 
x_129 = lean_nat_dec_le(x_122, x_122);
if (x_129 == 0)
{
uint8_t x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_122);
lean_dec(x_76);
lean_dec(x_8);
x_130 = 1;
x_131 = lean_box(x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_121);
if (lean_is_scalar(x_80)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_80;
}
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_85);
return x_133;
}
else
{
size_t x_134; size_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_80);
x_134 = 0;
x_135 = lean_usize_of_nat(x_122);
lean_dec(x_122);
x_136 = lean_box(0);
x_137 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate___spec__6(x_76, x_134, x_135, x_136, x_8, x_121, x_85);
lean_dec(x_8);
lean_dec(x_76);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_140 = x_137;
} else {
 lean_dec_ref(x_137);
 x_140 = lean_box(0);
}
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_142 = x_138;
} else {
 lean_dec_ref(x_138);
 x_142 = lean_box(0);
}
x_143 = 1;
x_144 = lean_box(x_143);
if (lean_is_scalar(x_142)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_142;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_141);
if (lean_is_scalar(x_140)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_140;
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_139);
return x_146;
}
}
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_202; 
x_170 = lean_ctor_get(x_78, 0);
x_171 = lean_ctor_get(x_78, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_78);
x_202 = lean_unbox(x_170);
lean_dec(x_170);
if (x_202 == 0)
{
lean_object* x_203; 
lean_dec(x_80);
lean_dec(x_76);
x_203 = l_Lake_buildUnlessUpToDate_x3f_go(x_4, x_5, x_12, x_6, x_8, x_171, x_79);
return x_203;
}
else
{
lean_object* x_204; uint8_t x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; 
lean_dec(x_12);
lean_dec(x_4);
x_204 = lean_ctor_get(x_171, 0);
lean_inc(x_204);
x_205 = lean_ctor_get_uint8(x_171, sizeof(void*)*1);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 x_206 = x_171;
} else {
 lean_dec_ref(x_171);
 x_206 = lean_box(0);
}
x_207 = l_Lake_instOrdJobAction;
x_208 = 1;
x_209 = lean_box(x_205);
x_210 = lean_box(x_208);
x_211 = l_instDecidableRelLe___rarg(x_207, x_209, x_210);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
if (lean_is_scalar(x_206)) {
 x_212 = lean_alloc_ctor(0, 1, 1);
} else {
 x_212 = x_206;
}
lean_ctor_set(x_212, 0, x_204);
lean_ctor_set_uint8(x_212, sizeof(void*)*1, x_205);
x_213 = lean_box(0);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_212);
x_172 = x_214;
x_173 = x_79;
goto block_201;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
if (lean_is_scalar(x_206)) {
 x_215 = lean_alloc_ctor(0, 1, 1);
} else {
 x_215 = x_206;
}
lean_ctor_set(x_215, 0, x_204);
lean_ctor_set_uint8(x_215, sizeof(void*)*1, x_208);
x_216 = lean_box(0);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_215);
x_172 = x_217;
x_173 = x_79;
goto block_201;
}
}
block_201:
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
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
x_176 = lean_array_get_size(x_76);
x_177 = lean_unsigned_to_nat(0u);
x_178 = lean_nat_dec_lt(x_177, x_176);
if (x_178 == 0)
{
uint8_t x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_176);
lean_dec(x_76);
lean_dec(x_8);
x_179 = 1;
x_180 = lean_box(x_179);
if (lean_is_scalar(x_175)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_175;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_174);
if (lean_is_scalar(x_80)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_80;
}
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_173);
return x_182;
}
else
{
uint8_t x_183; 
x_183 = lean_nat_dec_le(x_176, x_176);
if (x_183 == 0)
{
uint8_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_176);
lean_dec(x_76);
lean_dec(x_8);
x_184 = 1;
x_185 = lean_box(x_184);
if (lean_is_scalar(x_175)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_175;
}
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_174);
if (lean_is_scalar(x_80)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_80;
}
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_173);
return x_187;
}
else
{
size_t x_188; size_t x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_175);
lean_dec(x_80);
x_188 = 0;
x_189 = lean_usize_of_nat(x_176);
lean_dec(x_176);
x_190 = lean_box(0);
x_191 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate___spec__6(x_76, x_188, x_189, x_190, x_8, x_174, x_173);
lean_dec(x_8);
lean_dec(x_76);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_194 = x_191;
} else {
 lean_dec_ref(x_191);
 x_194 = lean_box(0);
}
x_195 = lean_ctor_get(x_192, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_196 = x_192;
} else {
 lean_dec_ref(x_192);
 x_196 = lean_box(0);
}
x_197 = 1;
x_198 = lean_box(x_197);
if (lean_is_scalar(x_196)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_196;
}
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_195);
if (lean_is_scalar(x_194)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_194;
}
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_193);
return x_200;
}
}
}
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_260; 
x_218 = lean_ctor_get(x_15, 0);
lean_inc(x_218);
lean_dec(x_15);
x_219 = lean_ctor_get(x_13, 1);
lean_inc(x_219);
lean_dec(x_13);
x_220 = lean_ctor_get(x_218, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_218, 1);
lean_inc(x_221);
lean_dec(x_218);
x_222 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_222, 0, x_220);
lean_inc(x_4);
x_223 = l_Lake_checkHashUpToDate___at_Lake_buildFileUnlessUpToDate___spec__4(x_3, x_4, x_222, x_7, x_8, x_219, x_14);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
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
x_227 = lean_ctor_get(x_224, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_224, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_229 = x_224;
} else {
 lean_dec_ref(x_224);
 x_229 = lean_box(0);
}
x_260 = lean_unbox(x_227);
lean_dec(x_227);
if (x_260 == 0)
{
lean_object* x_261; 
lean_dec(x_229);
lean_dec(x_226);
lean_dec(x_221);
x_261 = l_Lake_buildUnlessUpToDate_x3f_go(x_4, x_5, x_12, x_6, x_8, x_228, x_225);
return x_261;
}
else
{
lean_object* x_262; uint8_t x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; 
lean_dec(x_12);
lean_dec(x_4);
x_262 = lean_ctor_get(x_228, 0);
lean_inc(x_262);
x_263 = lean_ctor_get_uint8(x_228, sizeof(void*)*1);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 x_264 = x_228;
} else {
 lean_dec_ref(x_228);
 x_264 = lean_box(0);
}
x_265 = l_Lake_instOrdJobAction;
x_266 = 1;
x_267 = lean_box(x_263);
x_268 = lean_box(x_266);
x_269 = l_instDecidableRelLe___rarg(x_265, x_267, x_268);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
if (lean_is_scalar(x_264)) {
 x_270 = lean_alloc_ctor(0, 1, 1);
} else {
 x_270 = x_264;
}
lean_ctor_set(x_270, 0, x_262);
lean_ctor_set_uint8(x_270, sizeof(void*)*1, x_263);
x_271 = lean_box(0);
if (lean_is_scalar(x_229)) {
 x_272 = lean_alloc_ctor(0, 2, 0);
} else {
 x_272 = x_229;
}
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_270);
x_230 = x_272;
x_231 = x_225;
goto block_259;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
if (lean_is_scalar(x_264)) {
 x_273 = lean_alloc_ctor(0, 1, 1);
} else {
 x_273 = x_264;
}
lean_ctor_set(x_273, 0, x_262);
lean_ctor_set_uint8(x_273, sizeof(void*)*1, x_266);
x_274 = lean_box(0);
if (lean_is_scalar(x_229)) {
 x_275 = lean_alloc_ctor(0, 2, 0);
} else {
 x_275 = x_229;
}
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_273);
x_230 = x_275;
x_231 = x_225;
goto block_259;
}
}
block_259:
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_233 = x_230;
} else {
 lean_dec_ref(x_230);
 x_233 = lean_box(0);
}
x_234 = lean_array_get_size(x_221);
x_235 = lean_unsigned_to_nat(0u);
x_236 = lean_nat_dec_lt(x_235, x_234);
if (x_236 == 0)
{
uint8_t x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_234);
lean_dec(x_221);
lean_dec(x_8);
x_237 = 1;
x_238 = lean_box(x_237);
if (lean_is_scalar(x_233)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_233;
}
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_232);
if (lean_is_scalar(x_226)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_226;
}
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_231);
return x_240;
}
else
{
uint8_t x_241; 
x_241 = lean_nat_dec_le(x_234, x_234);
if (x_241 == 0)
{
uint8_t x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_234);
lean_dec(x_221);
lean_dec(x_8);
x_242 = 1;
x_243 = lean_box(x_242);
if (lean_is_scalar(x_233)) {
 x_244 = lean_alloc_ctor(0, 2, 0);
} else {
 x_244 = x_233;
}
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_232);
if (lean_is_scalar(x_226)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_226;
}
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_231);
return x_245;
}
else
{
size_t x_246; size_t x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_233);
lean_dec(x_226);
x_246 = 0;
x_247 = lean_usize_of_nat(x_234);
lean_dec(x_234);
x_248 = lean_box(0);
x_249 = l_Array_foldlMUnsafe_fold___at_Lake_buildFileUnlessUpToDate___spec__6(x_221, x_246, x_247, x_248, x_8, x_232, x_231);
lean_dec(x_8);
lean_dec(x_221);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 x_252 = x_249;
} else {
 lean_dec_ref(x_249);
 x_252 = lean_box(0);
}
x_253 = lean_ctor_get(x_250, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_254 = x_250;
} else {
 lean_dec_ref(x_250);
 x_254 = lean_box(0);
}
x_255 = 1;
x_256 = lean_box(x_255);
if (lean_is_scalar(x_254)) {
 x_257 = lean_alloc_ctor(0, 2, 0);
} else {
 x_257 = x_254;
}
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_253);
if (lean_is_scalar(x_252)) {
 x_258 = lean_alloc_ctor(0, 2, 0);
} else {
 x_258 = x_252;
}
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_251);
return x_258;
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
x_1 = lean_mk_string_unchecked(".trace", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_8 = l_Lake_buildFileUnlessUpToDate___closed__1;
lean_inc(x_1);
x_9 = lean_string_append(x_1, x_8);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
x_11 = 3;
lean_inc(x_5);
lean_inc(x_1);
x_12 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_buildFileUnlessUpToDate___spec__2(x_1, x_3, x_1, x_2, x_9, x_11, x_10, x_5, x_6, x_7);
lean_dec(x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lake_fetchFileTrace(x_1, x_4, x_5, x_15, x_14);
lean_dec(x_5);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_5);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_12, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
return x_12;
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
lean_ctor_set(x_12, 0, x_22);
return x_12;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
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
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(1, 2, 0);
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
}
else
{
uint8_t x_29; 
lean_dec(x_5);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_12);
if (x_29 == 0)
{
return x_12;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_12, 0);
x_31 = lean_ctor_get(x_12, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_12);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
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
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at_Lake_buildFileUnlessUpToDate___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_6);
lean_dec(x_6);
x_12 = l_Lake_buildUnlessUpToDate_x3f___at_Lake_buildFileUnlessUpToDate___spec__2(x_1, x_2, x_3, x_4, x_5, x_11, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileUnlessUpToDate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lake_buildFileUnlessUpToDate(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
return x_9;
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
x_1 = lean_mk_string_unchecked("Init.Data.String.Extra", 22, 22);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String.fromUTF8!", 16, 16);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid UTF-8 string", 20, 20);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__2;
x_2 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1___closed__3;
x_3 = lean_unsigned_to_nat(100u);
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
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lake_BuildTrace_mix(x_1, x_6);
x_11 = lean_apply_1(x_2, x_3);
lean_inc(x_4);
x_12 = l_Lake_buildFileUnlessUpToDate(x_4, x_10, x_11, x_5, x_7, x_8, x_9);
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
lean_ctor_set(x_18, 0, x_4);
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
lean_ctor_set(x_21, 0, x_4);
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
lean_ctor_set(x_27, 0, x_4);
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
lean_dec(x_4);
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
lean_dec(x_4);
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
x_1 = lean_mk_string_unchecked("stdout/stderr:\n", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___rarg___lambda__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
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
x_12 = lean_box(x_3);
x_13 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___rarg___lambda__1___boxed), 9, 5);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_10);
lean_closure_set(x_13, 3, x_2);
lean_closure_set(x_13, 4, x_12);
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_13);
x_15 = 1;
lean_inc(x_5);
x_16 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1(x_14, x_15, x_5, x_9, x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
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
x_23 = lean_string_utf8_byte_size(x_21);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_eq(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; uint8_t x_35; 
x_26 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_21, x_23, x_24);
x_27 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_21, x_26, x_23);
x_28 = lean_string_utf8_extract(x_21, x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_21);
x_29 = l_Lake_buildFileAfterDep___rarg___lambda__3___closed__1;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = l_Lake_BuildMetadata_fromJson_x3f___closed__1;
x_32 = lean_string_append(x_30, x_31);
x_33 = 1;
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_33);
x_35 = !lean_is_exclusive(x_20);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_20, 0);
x_37 = lean_array_push(x_36, x_34);
lean_ctor_set(x_20, 0, x_37);
x_38 = lean_box(0);
x_39 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_22, x_38, x_5, x_20, x_19);
lean_dec(x_5);
return x_39;
}
else
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_20, 0);
x_41 = lean_ctor_get_uint8(x_20, sizeof(void*)*1);
lean_inc(x_40);
lean_dec(x_20);
x_42 = lean_array_push(x_40, x_34);
x_43 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_41);
x_44 = lean_box(0);
x_45 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_22, x_44, x_5, x_43, x_19);
lean_dec(x_5);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_23);
lean_dec(x_21);
x_46 = lean_box(0);
x_47 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_22, x_46, x_5, x_20, x_19);
lean_dec(x_5);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_5);
x_48 = !lean_is_exclusive(x_16);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_16, 0);
lean_dec(x_49);
x_50 = !lean_is_exclusive(x_17);
if (x_50 == 0)
{
return x_16;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_17, 0);
x_52 = lean_ctor_get(x_17, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_17);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_16, 0, x_53);
return x_16;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_16, 1);
lean_inc(x_54);
lean_dec(x_16);
x_55 = lean_ctor_get(x_17, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_17, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_57 = x_17;
} else {
 lean_dec_ref(x_17);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_54);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_5);
x_60 = !lean_is_exclusive(x_16);
if (x_60 == 0)
{
return x_16;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_16, 0);
x_62 = lean_ctor_get(x_16, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_16);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_6);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_6);
lean_ctor_set(x_65, 1, x_7);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_6, 0);
x_67 = lean_ctor_get(x_6, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_6);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_7);
return x_69;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_box(x_5);
x_12 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___rarg___lambda__3___boxed), 7, 5);
lean_closure_set(x_12, 0, x_3);
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_11);
lean_closure_set(x_12, 3, x_4);
lean_closure_set(x_12, 4, x_6);
x_13 = l_Task_Priority_default;
x_14 = 0;
x_15 = lean_io_map_task(x_12, x_9, x_13, x_14, x_7);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_2, 0, x_17);
lean_ctor_set(x_15, 0, x_2);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_15);
lean_ctor_set(x_2, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_free_object(x_2);
lean_dec(x_10);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_2);
x_28 = lean_box(x_5);
x_29 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___rarg___lambda__3___boxed), 7, 5);
lean_closure_set(x_29, 0, x_3);
lean_closure_set(x_29, 1, x_1);
lean_closure_set(x_29, 2, x_28);
lean_closure_set(x_29, 3, x_4);
lean_closure_set(x_29, 4, x_6);
x_30 = l_Task_Priority_default;
x_31 = 0;
x_32 = lean_io_map_task(x_29, x_25, x_30, x_31, x_7);
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
x_36 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_26);
lean_ctor_set_uint8(x_36, sizeof(void*)*2, x_27);
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
lean_dec(x_26);
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
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___rarg___boxed), 7, 0);
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
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = l_Lake_buildFileAfterDep___rarg___lambda__1(x_1, x_2, x_3, x_4, x_10, x_6, x_7, x_8, x_9);
return x_11;
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
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = l_Lake_buildFileAfterDep___rarg___lambda__3(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDep___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Lake_buildFileAfterDep___rarg(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepList___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lake_BuildJob_collectList___rarg(x_2);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_box(x_5);
x_13 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___rarg___lambda__3___boxed), 7, 5);
lean_closure_set(x_13, 0, x_3);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_12);
lean_closure_set(x_13, 3, x_4);
lean_closure_set(x_13, 4, x_6);
x_14 = l_Task_Priority_default;
x_15 = 0;
x_16 = lean_io_map_task(x_13, x_10, x_14, x_15, x_7);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_ctor_set(x_8, 0, x_18);
lean_ctor_set(x_16, 0, x_8);
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
lean_ctor_set(x_8, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_free_object(x_8);
lean_dec(x_11);
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
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_8, 0);
x_27 = lean_ctor_get(x_8, 1);
x_28 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_8);
x_29 = lean_box(x_5);
x_30 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___rarg___lambda__3___boxed), 7, 5);
lean_closure_set(x_30, 0, x_3);
lean_closure_set(x_30, 1, x_1);
lean_closure_set(x_30, 2, x_29);
lean_closure_set(x_30, 3, x_4);
lean_closure_set(x_30, 4, x_6);
x_31 = l_Task_Priority_default;
x_32 = 0;
x_33 = lean_io_map_task(x_30, x_26, x_31, x_32, x_7);
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
x_37 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_27);
lean_ctor_set_uint8(x_37, sizeof(void*)*2, x_28);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_27);
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
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDepList___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepList___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Lake_buildFileAfterDepList___rarg(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepArray___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lake_BuildJob_collectArray___rarg(x_2);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_box(x_5);
x_13 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___rarg___lambda__3___boxed), 7, 5);
lean_closure_set(x_13, 0, x_3);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_12);
lean_closure_set(x_13, 3, x_4);
lean_closure_set(x_13, 4, x_6);
x_14 = l_Task_Priority_default;
x_15 = 0;
x_16 = lean_io_map_task(x_13, x_10, x_14, x_15, x_7);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_ctor_set(x_8, 0, x_18);
lean_ctor_set(x_16, 0, x_8);
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
lean_ctor_set(x_8, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_free_object(x_8);
lean_dec(x_11);
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
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_8, 0);
x_27 = lean_ctor_get(x_8, 1);
x_28 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_8);
x_29 = lean_box(x_5);
x_30 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDep___rarg___lambda__3___boxed), 7, 5);
lean_closure_set(x_30, 0, x_3);
lean_closure_set(x_30, 1, x_1);
lean_closure_set(x_30, 2, x_29);
lean_closure_set(x_30, 3, x_4);
lean_closure_set(x_30, 4, x_6);
x_31 = l_Task_Priority_default;
x_32 = 0;
x_33 = lean_io_map_task(x_30, x_26, x_31, x_32, x_7);
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
x_37 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_27);
lean_ctor_set_uint8(x_37, sizeof(void*)*2, x_28);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_27);
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
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_buildFileAfterDepArray___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_buildFileAfterDepArray___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Lake_buildFileAfterDepArray___rarg(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___at_Lake_inputBinFile___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_19 = l_Lake_buildFileAfterDep___rarg___lambda__3___closed__1;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_21 = l_Lake_BuildMetadata_fromJson_x3f___closed__1;
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
x_29 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_12, x_28, x_2, x_10, x_9);
lean_dec(x_2);
return x_29;
}
else
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_10, 0);
x_31 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
lean_inc(x_30);
lean_dec(x_10);
x_32 = lean_array_push(x_30, x_24);
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_31);
x_34 = lean_box(0);
x_35 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_12, x_34, x_2, x_33, x_9);
lean_dec(x_2);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_13);
lean_dec(x_11);
x_36 = lean_box(0);
x_37 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_12, x_36, x_2, x_10, x_9);
lean_dec(x_2);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_6);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_6, 0);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_7);
if (x_40 == 0)
{
return x_6;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_7, 0);
x_42 = lean_ctor_get(x_7, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_7);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_6, 0, x_43);
return x_6;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_6, 1);
lean_inc(x_44);
lean_dec(x_6);
x_45 = lean_ctor_get(x_7, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_7, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_47 = x_7;
} else {
 lean_dec_ref(x_7);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_44);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_6);
if (x_50 == 0)
{
return x_6;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_6, 0);
x_52 = lean_ctor_get(x_6, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_6);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
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
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lake_BuildMetadata_fromJson_x3f___closed__1;
x_12 = 0;
x_13 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_12);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = l_Lake_BuildMetadata_fromJson_x3f___closed__1;
x_17 = 0;
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
return x_8;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_8);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
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
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lake_BuildMetadata_fromJson_x3f___closed__1;
x_12 = 0;
x_13 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_12);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = l_Lake_BuildMetadata_fromJson_x3f___closed__1;
x_17 = 0;
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
return x_8;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_8);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
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
LEAN_EXPORT lean_object* l_Lake_inputFile(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (x_2 == 0)
{
lean_object* x_5; 
x_5 = l_Lake_inputBinFile(x_1, x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = l_Lake_inputTextFile(x_1, x_3, x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lake_inputFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lake_inputFile(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT uint64_t l_Array_foldlMUnsafe_fold___at_Lake_buildO___spec__1(lean_object* x_1, size_t x_2, size_t x_3, uint64_t x_4) {
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
static uint64_t _init_l_Lake_buildO___lambda__1___closed__3() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = 1723;
x_2 = l_Lake_platformTrace;
x_3 = lean_uint64_mix_hash(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_buildO___lambda__1___closed__4___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_Lake_buildO___lambda__1___closed__3;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_buildO___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_buildO___lambda__1___closed__2;
x_2 = l_Lake_buildO___lambda__1___closed__4___boxed__const__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_buildO___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
x_9 = l_Lake_buildO___lambda__1___closed__4;
x_10 = l_Lake_BuildTrace_mix(x_2, x_9);
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
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_6, x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
x_14 = l_Lake_buildO___lambda__1___closed__4;
x_15 = l_Lake_BuildTrace_mix(x_2, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_5);
return x_17;
}
else
{
size_t x_18; size_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_20 = l_Lake_Hash_nil;
x_21 = l_Array_foldlMUnsafe_fold___at_Lake_buildO___spec__1(x_1, x_18, x_19, x_20);
x_22 = l_Lake_platformTrace;
x_23 = lean_uint64_mix_hash(x_21, x_22);
x_24 = l_Lake_buildO___lambda__1___closed__2;
x_25 = lean_box_uint64(x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lake_BuildTrace_mix(x_2, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_4);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_5);
return x_29;
}
}
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_11 = l_Lake_BuildTrace_mix(x_1, x_7);
x_12 = l_Array_append___rarg(x_2, x_3);
lean_inc(x_4);
x_13 = lean_alloc_closure((void*)(l_Lake_buildO___lambda__2___boxed), 7, 4);
lean_closure_set(x_13, 0, x_4);
lean_closure_set(x_13, 1, x_5);
lean_closure_set(x_13, 2, x_12);
lean_closure_set(x_13, 3, x_6);
x_14 = 0;
lean_inc(x_4);
x_15 = l_Lake_buildFileUnlessUpToDate(x_4, x_11, x_13, x_14, x_8, x_9, x_10);
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
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_16, 0, x_21);
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_15, 0, x_25);
return x_15;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_dec(x_15);
x_27 = lean_ctor_get(x_16, 0);
lean_inc(x_27);
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
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_30, 1, x_27);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_26);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_15);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_15, 0);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_16);
if (x_35 == 0)
{
return x_15;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_16, 0);
x_37 = lean_ctor_get(x_16, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_16);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_15, 0, x_38);
return x_15;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_15, 1);
lean_inc(x_39);
lean_dec(x_15);
x_40 = lean_ctor_get(x_16, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_16, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_42 = x_16;
} else {
 lean_dec_ref(x_16);
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
lean_dec(x_4);
x_45 = !lean_is_exclusive(x_15);
if (x_45 == 0)
{
return x_15;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_15, 0);
x_47 = lean_ctor_get(x_15, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_15);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
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
x_23 = lean_string_utf8_byte_size(x_21);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_eq(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; uint8_t x_35; 
x_26 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_21, x_23, x_24);
x_27 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_21, x_26, x_23);
x_28 = lean_string_utf8_extract(x_21, x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_21);
x_29 = l_Lake_buildFileAfterDep___rarg___lambda__3___closed__1;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = l_Lake_BuildMetadata_fromJson_x3f___closed__1;
x_32 = lean_string_append(x_30, x_31);
x_33 = 1;
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_33);
x_35 = !lean_is_exclusive(x_20);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_20, 0);
x_37 = lean_array_push(x_36, x_34);
lean_ctor_set(x_20, 0, x_37);
x_38 = lean_box(0);
x_39 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_22, x_38, x_6, x_20, x_19);
lean_dec(x_6);
return x_39;
}
else
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_20, 0);
x_41 = lean_ctor_get_uint8(x_20, sizeof(void*)*1);
lean_inc(x_40);
lean_dec(x_20);
x_42 = lean_array_push(x_40, x_34);
x_43 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_41);
x_44 = lean_box(0);
x_45 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_22, x_44, x_6, x_43, x_19);
lean_dec(x_6);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_23);
lean_dec(x_21);
x_46 = lean_box(0);
x_47 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_22, x_46, x_6, x_20, x_19);
lean_dec(x_6);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_6);
x_48 = !lean_is_exclusive(x_16);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_16, 0);
lean_dec(x_49);
x_50 = !lean_is_exclusive(x_17);
if (x_50 == 0)
{
return x_16;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_17, 0);
x_52 = lean_ctor_get(x_17, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_17);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_16, 0, x_53);
return x_16;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_16, 1);
lean_inc(x_54);
lean_dec(x_16);
x_55 = lean_ctor_get(x_17, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_17, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_57 = x_17;
} else {
 lean_dec_ref(x_17);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_54);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_6);
x_60 = !lean_is_exclusive(x_16);
if (x_60 == 0)
{
return x_16;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_16, 0);
x_62 = lean_ctor_get(x_16, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_16);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_7);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_7);
lean_ctor_set(x_65, 1, x_8);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_7, 0);
x_67 = lean_ctor_get(x_7, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_7);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_8);
return x_69;
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
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_2, 0);
x_28 = lean_ctor_get(x_2, 1);
x_29 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_2);
x_30 = lean_alloc_closure((void*)(l_Lake_buildO___lambda__4), 8, 6);
lean_closure_set(x_30, 0, x_3);
lean_closure_set(x_30, 1, x_4);
lean_closure_set(x_30, 2, x_1);
lean_closure_set(x_30, 3, x_5);
lean_closure_set(x_30, 4, x_10);
lean_closure_set(x_30, 5, x_7);
x_31 = l_Task_Priority_default;
x_32 = 0;
x_33 = lean_io_map_task(x_30, x_27, x_31, x_32, x_8);
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
x_37 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_28);
lean_ctor_set_uint8(x_37, sizeof(void*)*2, x_29);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_28);
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
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_buildO___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lake_buildO___spec__1(x_1, x_5, x_6, x_7);
lean_dec(x_1);
x_9 = lean_box_uint64(x_8);
return x_9;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_4, 1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanO___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_5, 16);
lean_inc(x_9);
x_10 = l_Array_append___rarg(x_9, x_1);
x_11 = l_Array_append___rarg(x_10, x_2);
x_12 = lean_ctor_get(x_5, 12);
lean_inc(x_12);
lean_dec(x_5);
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = l_Lake_compileO(x_3, x_4, x_11, x_12, x_14, x_8);
lean_dec(x_11);
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
lean_object* x_20; 
x_20 = lean_ctor_get(x_16, 1);
lean_ctor_set(x_7, 0, x_20);
lean_ctor_set(x_16, 1, x_7);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_16);
lean_ctor_set(x_7, 0, x_22);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_7);
lean_ctor_set(x_15, 0, x_23);
return x_15;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_27 = x_16;
} else {
 lean_dec_ref(x_16);
 x_27 = lean_box(0);
}
lean_ctor_set(x_7, 0, x_26);
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_27;
}
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_7);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_24);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_15, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_16);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_16, 1);
lean_ctor_set(x_7, 0, x_33);
lean_ctor_set(x_16, 1, x_7);
return x_15;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_16, 0);
x_35 = lean_ctor_get(x_16, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_16);
lean_ctor_set(x_7, 0, x_35);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_7);
lean_ctor_set(x_15, 0, x_36);
return x_15;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_15, 1);
lean_inc(x_37);
lean_dec(x_15);
x_38 = lean_ctor_get(x_16, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_16, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_40 = x_16;
} else {
 lean_dec_ref(x_16);
 x_40 = lean_box(0);
}
lean_ctor_set(x_7, 0, x_39);
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_7);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
return x_42;
}
}
}
else
{
lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_7, 0);
x_44 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
lean_inc(x_43);
lean_dec(x_7);
x_45 = l_Lake_compileO(x_3, x_4, x_11, x_12, x_43, x_8);
lean_dec(x_11);
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
x_52 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_44);
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
x_60 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_44);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
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
x_14 = 0;
lean_inc(x_4);
x_15 = l_Lake_buildFileUnlessUpToDate(x_4, x_10, x_13, x_14, x_7, x_8, x_9);
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
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_16, 0, x_21);
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_15, 0, x_25);
return x_15;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_dec(x_15);
x_27 = lean_ctor_get(x_16, 0);
lean_inc(x_27);
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
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_30, 1, x_27);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_26);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_15);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_15, 0);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_16);
if (x_35 == 0)
{
return x_15;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_16, 0);
x_37 = lean_ctor_get(x_16, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_16);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_15, 0, x_38);
return x_15;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_15, 1);
lean_inc(x_39);
lean_dec(x_15);
x_40 = lean_ctor_get(x_16, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_16, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_42 = x_16;
} else {
 lean_dec_ref(x_16);
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
lean_dec(x_4);
x_45 = !lean_is_exclusive(x_15);
if (x_45 == 0)
{
return x_15;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_15, 0);
x_47 = lean_ctor_get(x_15, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_15);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
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
x_22 = lean_string_utf8_byte_size(x_20);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_eq(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; 
x_25 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_20, x_22, x_23);
x_26 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_20, x_25, x_22);
x_27 = lean_string_utf8_extract(x_20, x_25, x_26);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_20);
x_28 = l_Lake_buildFileAfterDep___rarg___lambda__3___closed__1;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l_Lake_BuildMetadata_fromJson_x3f___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = 1;
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
x_34 = !lean_is_exclusive(x_19);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_19, 0);
x_36 = lean_array_push(x_35, x_33);
lean_ctor_set(x_19, 0, x_36);
x_37 = lean_box(0);
x_38 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_21, x_37, x_5, x_19, x_18);
lean_dec(x_5);
return x_38;
}
else
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_19, 0);
x_40 = lean_ctor_get_uint8(x_19, sizeof(void*)*1);
lean_inc(x_39);
lean_dec(x_19);
x_41 = lean_array_push(x_39, x_33);
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_40);
x_43 = lean_box(0);
x_44 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_21, x_43, x_5, x_42, x_18);
lean_dec(x_5);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_22);
lean_dec(x_20);
x_45 = lean_box(0);
x_46 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_21, x_45, x_5, x_19, x_18);
lean_dec(x_5);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_5);
x_47 = !lean_is_exclusive(x_15);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_15, 0);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_16);
if (x_49 == 0)
{
return x_15;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_16, 0);
x_51 = lean_ctor_get(x_16, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_16);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_15, 0, x_52);
return x_15;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_15, 1);
lean_inc(x_53);
lean_dec(x_15);
x_54 = lean_ctor_get(x_16, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_16, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_56 = x_16;
} else {
 lean_dec_ref(x_16);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_53);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_5);
x_59 = !lean_is_exclusive(x_15);
if (x_59 == 0)
{
return x_15;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_15, 0);
x_61 = lean_ctor_get(x_15, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_15);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_6);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_6);
lean_ctor_set(x_64, 1, x_7);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_6, 0);
x_66 = lean_ctor_get(x_6, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_6);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_7);
return x_68;
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
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
x_28 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_2);
x_29 = lean_alloc_closure((void*)(l_Lake_buildLeanO___lambda__5), 7, 5);
lean_closure_set(x_29, 0, x_3);
lean_closure_set(x_29, 1, x_4);
lean_closure_set(x_29, 2, x_1);
lean_closure_set(x_29, 3, x_9);
lean_closure_set(x_29, 4, x_5);
x_30 = l_Task_Priority_default;
x_31 = 0;
x_32 = lean_io_map_task(x_29, x_26, x_30, x_31, x_6);
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
x_36 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_27);
lean_ctor_set_uint8(x_36, sizeof(void*)*2, x_28);
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
lean_dec(x_27);
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
lean_dec(x_1);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_8 = l_Lake_BuildTrace_mix(x_1, x_4);
lean_inc(x_2);
x_9 = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lambda__2___boxed), 6, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_3);
x_10 = l_Lake_buildStaticLib___lambda__3___closed__1;
x_11 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_9);
x_12 = 0;
lean_inc(x_2);
x_13 = l_Lake_buildFileUnlessUpToDate(x_2, x_8, x_11, x_12, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_14, 0, x_19);
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_13, 0, x_23);
return x_13;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_dec(x_13);
x_25 = lean_ctor_get(x_14, 0);
lean_inc(x_25);
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
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_25);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_24);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_13);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_13, 0);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_14);
if (x_33 == 0)
{
return x_13;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_14, 0);
x_35 = lean_ctor_get(x_14, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_14);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_13, 0, x_36);
return x_13;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_13, 1);
lean_inc(x_37);
lean_dec(x_13);
x_38 = lean_ctor_get(x_14, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_14, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_40 = x_14;
} else {
 lean_dec_ref(x_14);
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
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_13);
if (x_43 == 0)
{
return x_13;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_13, 0);
x_45 = lean_ctor_get(x_13, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_13);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
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
x_20 = lean_string_utf8_byte_size(x_18);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; uint8_t x_32; 
x_23 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_18, x_20, x_21);
x_24 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_18, x_23, x_20);
x_25 = lean_string_utf8_extract(x_18, x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_18);
x_26 = l_Lake_buildFileAfterDep___rarg___lambda__3___closed__1;
x_27 = lean_string_append(x_26, x_25);
lean_dec(x_25);
x_28 = l_Lake_BuildMetadata_fromJson_x3f___closed__1;
x_29 = lean_string_append(x_27, x_28);
x_30 = 1;
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_30);
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_17, 0);
x_34 = lean_array_push(x_33, x_31);
lean_ctor_set(x_17, 0, x_34);
x_35 = lean_box(0);
x_36 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_19, x_35, x_3, x_17, x_16);
lean_dec(x_3);
return x_36;
}
else
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_17, 0);
x_38 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
lean_inc(x_37);
lean_dec(x_17);
x_39 = lean_array_push(x_37, x_31);
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_38);
x_41 = lean_box(0);
x_42 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_19, x_41, x_3, x_40, x_16);
lean_dec(x_3);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_20);
lean_dec(x_18);
x_43 = lean_box(0);
x_44 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_19, x_43, x_3, x_17, x_16);
lean_dec(x_3);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_3);
x_45 = !lean_is_exclusive(x_13);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_13, 0);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_14);
if (x_47 == 0)
{
return x_13;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_14, 0);
x_49 = lean_ctor_get(x_14, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_14);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_13, 0, x_50);
return x_13;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_13, 1);
lean_inc(x_51);
lean_dec(x_13);
x_52 = lean_ctor_get(x_14, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_14, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_54 = x_14;
} else {
 lean_dec_ref(x_14);
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
lean_dec(x_3);
x_57 = !lean_is_exclusive(x_13);
if (x_57 == 0)
{
return x_13;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_13, 0);
x_59 = lean_ctor_get(x_13, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_13);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_4);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_4);
lean_ctor_set(x_62, 1, x_5);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_4, 0);
x_64 = lean_ctor_get(x_4, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_4);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_5);
return x_66;
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
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 1);
x_26 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_7);
x_27 = lean_alloc_closure((void*)(l_Lake_buildStaticLib___lambda__4), 5, 3);
lean_closure_set(x_27, 0, x_1);
lean_closure_set(x_27, 1, x_6);
lean_closure_set(x_27, 2, x_3);
x_28 = l_Task_Priority_default;
x_29 = 0;
x_30 = lean_io_map_task(x_27, x_24, x_28, x_29, x_4);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
x_34 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_25);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_26);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_25);
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_38 = x_30;
} else {
 lean_dec_ref(x_30);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
return x_39;
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
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_9 = lean_array_size(x_1);
x_10 = 0;
x_11 = l_Array_mapMUnsafe_map___at_Lake_compileStaticLib___spec__1(x_9, x_10, x_1);
x_12 = l_Array_append___rarg(x_11, x_2);
x_13 = l_Array_append___rarg(x_12, x_3);
x_14 = lean_ctor_get(x_5, 18);
lean_inc(x_14);
x_15 = l_Array_append___rarg(x_13, x_14);
lean_dec(x_14);
x_16 = lean_ctor_get(x_5, 12);
lean_inc(x_16);
lean_dec(x_5);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_7, 0);
x_19 = l_Lake_compileSharedLib(x_4, x_15, x_16, x_18, x_8);
lean_dec(x_15);
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
lean_ctor_set(x_7, 0, x_24);
lean_ctor_set(x_20, 1, x_7);
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
lean_ctor_set(x_7, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_7);
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
lean_ctor_set(x_7, 0, x_30);
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_29);
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
lean_ctor_set(x_7, 0, x_37);
lean_ctor_set(x_20, 1, x_7);
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
lean_ctor_set(x_7, 0, x_39);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_7);
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
lean_ctor_set(x_7, 0, x_43);
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_7);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
return x_46;
}
}
}
else
{
lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_7, 0);
x_48 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
lean_inc(x_47);
lean_dec(x_7);
x_49 = l_Lake_compileSharedLib(x_4, x_15, x_16, x_47, x_8);
lean_dec(x_15);
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
x_56 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_48);
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
x_64 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_48);
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
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLib___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
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
x_14 = 0;
lean_inc(x_5);
x_15 = l_Lake_buildFileUnlessUpToDate(x_5, x_10, x_13, x_14, x_7, x_8, x_9);
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
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_16, 0, x_21);
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_15, 0, x_25);
return x_15;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_dec(x_15);
x_27 = lean_ctor_get(x_16, 0);
lean_inc(x_27);
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
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_5);
lean_ctor_set(x_30, 1, x_27);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_26);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_5);
x_33 = !lean_is_exclusive(x_15);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_15, 0);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_16);
if (x_35 == 0)
{
return x_15;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_16, 0);
x_37 = lean_ctor_get(x_16, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_16);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_15, 0, x_38);
return x_15;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_15, 1);
lean_inc(x_39);
lean_dec(x_15);
x_40 = lean_ctor_get(x_16, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_16, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_42 = x_16;
} else {
 lean_dec_ref(x_16);
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
lean_dec(x_5);
x_45 = !lean_is_exclusive(x_15);
if (x_45 == 0)
{
return x_15;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_15, 0);
x_47 = lean_ctor_get(x_15, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_15);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
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
x_22 = lean_string_utf8_byte_size(x_20);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_eq(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; 
x_25 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_20, x_22, x_23);
x_26 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_20, x_25, x_22);
x_27 = lean_string_utf8_extract(x_20, x_25, x_26);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_20);
x_28 = l_Lake_buildFileAfterDep___rarg___lambda__3___closed__1;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l_Lake_BuildMetadata_fromJson_x3f___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = 1;
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
x_34 = !lean_is_exclusive(x_19);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_19, 0);
x_36 = lean_array_push(x_35, x_33);
lean_ctor_set(x_19, 0, x_36);
x_37 = lean_box(0);
x_38 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_21, x_37, x_5, x_19, x_18);
lean_dec(x_5);
return x_38;
}
else
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_19, 0);
x_40 = lean_ctor_get_uint8(x_19, sizeof(void*)*1);
lean_inc(x_39);
lean_dec(x_19);
x_41 = lean_array_push(x_39, x_33);
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_40);
x_43 = lean_box(0);
x_44 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_21, x_43, x_5, x_42, x_18);
lean_dec(x_5);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_22);
lean_dec(x_20);
x_45 = lean_box(0);
x_46 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_21, x_45, x_5, x_19, x_18);
lean_dec(x_5);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_5);
x_47 = !lean_is_exclusive(x_15);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_15, 0);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_16);
if (x_49 == 0)
{
return x_15;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_16, 0);
x_51 = lean_ctor_get(x_16, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_16);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_15, 0, x_52);
return x_15;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_15, 1);
lean_inc(x_53);
lean_dec(x_15);
x_54 = lean_ctor_get(x_16, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_16, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_56 = x_16;
} else {
 lean_dec_ref(x_16);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_53);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_5);
x_59 = !lean_is_exclusive(x_15);
if (x_59 == 0)
{
return x_15;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_15, 0);
x_61 = lean_ctor_get(x_15, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_15);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_6);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_6);
lean_ctor_set(x_64, 1, x_7);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_6, 0);
x_66 = lean_ctor_get(x_6, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_6);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_7);
return x_68;
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
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_10, 0);
x_28 = lean_ctor_get(x_10, 1);
x_29 = lean_ctor_get_uint8(x_10, sizeof(void*)*2);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_10);
x_30 = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLib___lambda__3), 7, 5);
lean_closure_set(x_30, 0, x_3);
lean_closure_set(x_30, 1, x_4);
lean_closure_set(x_30, 2, x_1);
lean_closure_set(x_30, 3, x_9);
lean_closure_set(x_30, 4, x_5);
x_31 = l_Task_Priority_default;
x_32 = 0;
x_33 = lean_io_map_task(x_30, x_27, x_31, x_32, x_6);
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
x_37 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_28);
lean_ctor_set_uint8(x_37, sizeof(void*)*2, x_29);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_28);
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
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
return x_42;
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
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint64_t x_10; 
x_7 = lean_array_get_size(x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_2 == 0)
{
uint64_t x_42; 
x_42 = 13;
x_10 = x_42;
goto block_41;
}
else
{
uint64_t x_43; 
x_43 = 11;
x_10 = x_43;
goto block_41;
}
block_41:
{
if (x_9 == 0)
{
uint64_t x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_7);
x_11 = l_Lake_buildO___lambda__1___closed__3;
x_12 = lean_uint64_mix_hash(x_10, x_11);
x_13 = l_Lake_buildO___lambda__1___closed__2;
x_14 = lean_box_uint64(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lake_BuildTrace_mix(x_3, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_6);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_7, x_7);
if (x_19 == 0)
{
uint64_t x_20; uint64_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_7);
x_20 = l_Lake_buildO___lambda__1___closed__3;
x_21 = lean_uint64_mix_hash(x_10, x_20);
x_22 = l_Lake_buildO___lambda__1___closed__2;
x_23 = lean_box_uint64(x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Lake_BuildTrace_mix(x_3, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_5);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_6);
return x_27;
}
else
{
size_t x_28; size_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_28 = 0;
x_29 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_30 = l_Lake_Hash_nil;
x_31 = l_Array_foldlMUnsafe_fold___at_Lake_buildO___spec__1(x_1, x_28, x_29, x_30);
x_32 = l_Lake_platformTrace;
x_33 = lean_uint64_mix_hash(x_31, x_32);
x_34 = lean_uint64_mix_hash(x_10, x_33);
x_35 = l_Lake_buildO___lambda__1___closed__2;
x_36 = lean_box_uint64(x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lake_BuildTrace_mix(x_3, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_5);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_6);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = l_Array_append___rarg(x_1, x_2);
x_11 = l_Lake_LeanInstall_ccLinkFlags(x_3, x_6);
x_12 = l_Array_append___rarg(x_10, x_11);
lean_dec(x_11);
x_13 = lean_ctor_get(x_6, 12);
lean_inc(x_13);
lean_dec(x_6);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = l_Lake_compileExe(x_4, x_5, x_12, x_13, x_15, x_9);
lean_dec(x_12);
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
lean_object* x_21; 
x_21 = lean_ctor_get(x_17, 1);
lean_ctor_set(x_8, 0, x_21);
lean_ctor_set(x_17, 1, x_8);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_17);
lean_ctor_set(x_8, 0, x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_8);
lean_ctor_set(x_16, 0, x_24);
return x_16;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_dec(x_16);
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_28 = x_17;
} else {
 lean_dec_ref(x_17);
 x_28 = lean_box(0);
}
lean_ctor_set(x_8, 0, x_27);
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_8);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_16, 0);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_17);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_17, 1);
lean_ctor_set(x_8, 0, x_34);
lean_ctor_set(x_17, 1, x_8);
return x_16;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_17, 0);
x_36 = lean_ctor_get(x_17, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_17);
lean_ctor_set(x_8, 0, x_36);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_8);
lean_ctor_set(x_16, 0, x_37);
return x_16;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_16, 1);
lean_inc(x_38);
lean_dec(x_16);
x_39 = lean_ctor_get(x_17, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_17, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_41 = x_17;
} else {
 lean_dec_ref(x_17);
 x_41 = lean_box(0);
}
lean_ctor_set(x_8, 0, x_40);
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_8);
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
lean_free_object(x_8);
x_44 = !lean_is_exclusive(x_16);
if (x_44 == 0)
{
return x_16;
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
return x_47;
}
}
}
else
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_8, 0);
x_49 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
lean_inc(x_48);
lean_dec(x_8);
x_50 = l_Lake_compileExe(x_4, x_5, x_12, x_13, x_48, x_9);
lean_dec(x_12);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
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
x_57 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_49);
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
x_65 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_49);
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
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_50, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_50, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_70 = x_50;
} else {
 lean_dec_ref(x_50);
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
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_11 = l_Lake_BuildTrace_mix(x_1, x_7);
x_12 = lean_box(x_4);
lean_inc(x_5);
x_13 = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lambda__2___boxed), 9, 5);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_3);
lean_closure_set(x_13, 2, x_12);
lean_closure_set(x_13, 3, x_5);
lean_closure_set(x_13, 4, x_6);
x_14 = l_Lake_buildLeanO___lambda__4___closed__1;
x_15 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_13);
x_16 = 0;
lean_inc(x_5);
x_17 = l_Lake_buildFileUnlessUpToDate(x_5, x_11, x_15, x_16, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
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
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_18, 0, x_23);
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_18);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_17, 0, x_27);
return x_17;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_dec(x_17);
x_29 = lean_ctor_get(x_18, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_31 = x_18;
} else {
 lean_dec_ref(x_18);
 x_31 = lean_box(0);
}
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_5);
lean_ctor_set(x_32, 1, x_29);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_28);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_5);
x_35 = !lean_is_exclusive(x_17);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_17, 0);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_18);
if (x_37 == 0)
{
return x_17;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_18, 0);
x_39 = lean_ctor_get(x_18, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_18);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_17, 0, x_40);
return x_17;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_17, 1);
lean_inc(x_41);
lean_dec(x_17);
x_42 = lean_ctor_get(x_18, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_18, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_44 = x_18;
} else {
 lean_dec_ref(x_18);
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
lean_dec(x_5);
x_47 = !lean_is_exclusive(x_17);
if (x_47 == 0)
{
return x_17;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_17, 0);
x_49 = lean_ctor_get(x_17, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_17);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lambda__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
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
x_13 = lean_box(x_3);
x_14 = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lambda__3___boxed), 10, 6);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_1);
lean_closure_set(x_14, 2, x_2);
lean_closure_set(x_14, 3, x_13);
lean_closure_set(x_14, 4, x_4);
lean_closure_set(x_14, 5, x_11);
x_15 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_15, 0, x_5);
lean_closure_set(x_15, 1, x_14);
x_16 = 1;
lean_inc(x_6);
x_17 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1(x_15, x_16, x_6, x_10, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
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
x_24 = lean_string_utf8_byte_size(x_22);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_eq(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; 
x_27 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_22, x_24, x_25);
x_28 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_22, x_27, x_24);
x_29 = lean_string_utf8_extract(x_22, x_27, x_28);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_22);
x_30 = l_Lake_buildFileAfterDep___rarg___lambda__3___closed__1;
x_31 = lean_string_append(x_30, x_29);
lean_dec(x_29);
x_32 = l_Lake_BuildMetadata_fromJson_x3f___closed__1;
x_33 = lean_string_append(x_31, x_32);
x_34 = 1;
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
x_36 = !lean_is_exclusive(x_21);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_21, 0);
x_38 = lean_array_push(x_37, x_35);
lean_ctor_set(x_21, 0, x_38);
x_39 = lean_box(0);
x_40 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_23, x_39, x_6, x_21, x_20);
lean_dec(x_6);
return x_40;
}
else
{
lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_21, 0);
x_42 = lean_ctor_get_uint8(x_21, sizeof(void*)*1);
lean_inc(x_41);
lean_dec(x_21);
x_43 = lean_array_push(x_41, x_35);
x_44 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_42);
x_45 = lean_box(0);
x_46 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_23, x_45, x_6, x_44, x_20);
lean_dec(x_6);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_24);
lean_dec(x_22);
x_47 = lean_box(0);
x_48 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_23, x_47, x_6, x_21, x_20);
lean_dec(x_6);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_6);
x_49 = !lean_is_exclusive(x_17);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_17, 0);
lean_dec(x_50);
x_51 = !lean_is_exclusive(x_18);
if (x_51 == 0)
{
return x_17;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_18, 0);
x_53 = lean_ctor_get(x_18, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_18);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_17, 0, x_54);
return x_17;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_17, 1);
lean_inc(x_55);
lean_dec(x_17);
x_56 = lean_ctor_get(x_18, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_18, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_58 = x_18;
} else {
 lean_dec_ref(x_18);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_55);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_6);
x_61 = !lean_is_exclusive(x_17);
if (x_61 == 0)
{
return x_17;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_17, 0);
x_63 = lean_ctor_get(x_17, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_17);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_7);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_7);
lean_ctor_set(x_66, 1, x_8);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_7, 0);
x_68 = lean_ctor_get(x_7, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_7);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_8);
return x_70;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_box(x_5);
lean_inc(x_4);
x_9 = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lambda__1___boxed), 6, 2);
lean_closure_set(x_9, 0, x_4);
lean_closure_set(x_9, 1, x_8);
x_10 = l_Lake_buildLeanO___closed__1;
x_11 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_9);
x_12 = l_Lake_BuildJob_collectArray___rarg(x_2);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_box(x_5);
x_17 = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lambda__4___boxed), 8, 6);
lean_closure_set(x_17, 0, x_3);
lean_closure_set(x_17, 1, x_4);
lean_closure_set(x_17, 2, x_16);
lean_closure_set(x_17, 3, x_1);
lean_closure_set(x_17, 4, x_11);
lean_closure_set(x_17, 5, x_6);
x_18 = l_Task_Priority_default;
x_19 = 0;
x_20 = lean_io_map_task(x_17, x_14, x_18, x_19, x_7);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_12, 0, x_22);
lean_ctor_set(x_20, 0, x_12);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_20);
lean_ctor_set(x_12, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_free_object(x_12);
lean_dec(x_15);
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_12, 0);
x_31 = lean_ctor_get(x_12, 1);
x_32 = lean_ctor_get_uint8(x_12, sizeof(void*)*2);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_12);
x_33 = lean_box(x_5);
x_34 = lean_alloc_closure((void*)(l_Lake_buildLeanExe___lambda__4___boxed), 8, 6);
lean_closure_set(x_34, 0, x_3);
lean_closure_set(x_34, 1, x_4);
lean_closure_set(x_34, 2, x_33);
lean_closure_set(x_34, 3, x_1);
lean_closure_set(x_34, 4, x_11);
lean_closure_set(x_34, 5, x_6);
x_35 = l_Task_Priority_default;
x_36 = 0;
x_37 = lean_io_map_task(x_34, x_30, x_35, x_36, x_7);
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
x_41 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_31);
lean_ctor_set_uint8(x_41, sizeof(void*)*2, x_32);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_31);
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
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l_Lake_buildLeanExe___lambda__1(x_1, x_7, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lake_buildLeanExe___lambda__2(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lake_buildLeanExe___lambda__3(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lake_buildLeanExe___lambda__4(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanExe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Lake_buildLeanExe(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
lean_dec(x_2);
return x_9;
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint64_t x_20; 
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
x_11 = lean_array_get_size(x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
x_14 = l_Array_append___rarg(x_2, x_3);
x_15 = l_Array_append___rarg(x_14, x_1);
x_16 = lean_ctor_get(x_6, 18);
lean_inc(x_16);
x_17 = l_Array_append___rarg(x_15, x_16);
lean_dec(x_16);
x_18 = lean_ctor_get(x_6, 12);
lean_inc(x_18);
lean_dec(x_6);
lean_inc(x_4);
x_19 = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLibOfStatic___lambda__1___boxed), 6, 3);
lean_closure_set(x_19, 0, x_4);
lean_closure_set(x_19, 1, x_17);
lean_closure_set(x_19, 2, x_18);
if (x_13 == 0)
{
uint64_t x_64; 
lean_dec(x_11);
x_64 = l_Lake_Hash_nil;
x_20 = x_64;
goto block_63;
}
else
{
uint8_t x_65; 
x_65 = lean_nat_dec_le(x_11, x_11);
if (x_65 == 0)
{
uint64_t x_66; 
lean_dec(x_11);
x_66 = l_Lake_Hash_nil;
x_20 = x_66;
goto block_63;
}
else
{
size_t x_67; size_t x_68; uint64_t x_69; uint64_t x_70; 
x_67 = 0;
x_68 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_69 = l_Lake_Hash_nil;
x_70 = l_Array_foldlMUnsafe_fold___at_Lake_buildO___spec__1(x_1, x_67, x_68, x_69);
x_20 = x_70;
goto block_63;
}
}
block_63:
{
uint64_t x_21; uint64_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_21 = l_Lake_platformTrace;
x_22 = lean_uint64_mix_hash(x_20, x_21);
x_23 = l_Lake_buildO___lambda__1___closed__2;
x_24 = lean_box_uint64(x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lake_BuildTrace_mix(x_10, x_25);
x_27 = l_Lake_BuildTrace_mix(x_5, x_26);
x_28 = 0;
lean_inc(x_4);
x_29 = l_Lake_buildFileUnlessUpToDate(x_4, x_27, x_19, x_28, x_7, x_8, x_9);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
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
x_34 = lean_ctor_get(x_30, 0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_4);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_30, 0, x_35);
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
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_4);
lean_ctor_set(x_38, 1, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
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
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_4);
lean_ctor_set(x_44, 1, x_41);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_40);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_4);
x_47 = !lean_is_exclusive(x_29);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_29, 0);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_30);
if (x_49 == 0)
{
return x_29;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_30, 0);
x_51 = lean_ctor_get(x_30, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_30);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_29, 0, x_52);
return x_29;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_29, 1);
lean_inc(x_53);
lean_dec(x_29);
x_54 = lean_ctor_get(x_30, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_30, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_56 = x_30;
} else {
 lean_dec_ref(x_30);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_53);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_4);
x_59 = !lean_is_exclusive(x_29);
if (x_59 == 0)
{
return x_29;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_29, 0);
x_61 = lean_ctor_get(x_29, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_29);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-Wl,--no-whole-archive", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-Wl,--whole-archive", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-Wl,-force_load,", 16, 16);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_67; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 1);
x_11 = l_Lake_sharedLibExt;
lean_inc(x_9);
x_12 = l_System_FilePath_withExtension(x_9, x_11);
x_67 = l_System_Platform_isOSX;
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__2;
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 1, x_68);
x_69 = l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__3;
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_6);
x_71 = lean_array_mk(x_70);
x_13 = x_71;
goto block_66;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_72 = l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__4;
x_73 = lean_string_append(x_72, x_9);
lean_dec(x_9);
x_74 = l_Lake_BuildMetadata_fromJson_x3f___closed__1;
x_75 = lean_string_append(x_73, x_74);
x_76 = lean_box(0);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 1, x_76);
lean_ctor_set(x_6, 0, x_75);
x_77 = lean_array_mk(x_6);
x_13 = x_77;
goto block_66;
}
block_66:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_14 = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLibOfStatic___lambda__2___boxed), 9, 5);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_13);
lean_closure_set(x_14, 2, x_2);
lean_closure_set(x_14, 3, x_12);
lean_closure_set(x_14, 4, x_10);
x_15 = l_Lake_buildLeanO___lambda__4___closed__1;
x_16 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_14);
x_17 = 1;
lean_inc(x_3);
x_18 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1(x_16, x_17, x_3, x_7, x_5);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_string_utf8_byte_size(x_23);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_nat_dec_eq(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; uint8_t x_37; 
x_28 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_23, x_25, x_26);
x_29 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_23, x_28, x_25);
x_30 = lean_string_utf8_extract(x_23, x_28, x_29);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_23);
x_31 = l_Lake_buildFileAfterDep___rarg___lambda__3___closed__1;
x_32 = lean_string_append(x_31, x_30);
lean_dec(x_30);
x_33 = l_Lake_BuildMetadata_fromJson_x3f___closed__1;
x_34 = lean_string_append(x_32, x_33);
x_35 = 1;
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_35);
x_37 = !lean_is_exclusive(x_22);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_22, 0);
x_39 = lean_array_push(x_38, x_36);
lean_ctor_set(x_22, 0, x_39);
x_40 = lean_box(0);
x_41 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_24, x_40, x_3, x_22, x_21);
lean_dec(x_3);
return x_41;
}
else
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_22, 0);
x_43 = lean_ctor_get_uint8(x_22, sizeof(void*)*1);
lean_inc(x_42);
lean_dec(x_22);
x_44 = lean_array_push(x_42, x_36);
x_45 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_43);
x_46 = lean_box(0);
x_47 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_24, x_46, x_3, x_45, x_21);
lean_dec(x_3);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_25);
lean_dec(x_23);
x_48 = lean_box(0);
x_49 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_24, x_48, x_3, x_22, x_21);
lean_dec(x_3);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_3);
x_50 = !lean_is_exclusive(x_18);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_18, 0);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_19);
if (x_52 == 0)
{
return x_18;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_19, 0);
x_54 = lean_ctor_get(x_19, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_19);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_18, 0, x_55);
return x_18;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_18, 1);
lean_inc(x_56);
lean_dec(x_18);
x_57 = lean_ctor_get(x_19, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_19, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_59 = x_19;
} else {
 lean_dec_ref(x_19);
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
else
{
uint8_t x_62; 
lean_dec(x_3);
x_62 = !lean_is_exclusive(x_18);
if (x_62 == 0)
{
return x_18;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_18, 0);
x_64 = lean_ctor_get(x_18, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_18);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_127; 
x_78 = lean_ctor_get(x_6, 0);
x_79 = lean_ctor_get(x_6, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_6);
x_80 = l_Lake_sharedLibExt;
lean_inc(x_78);
x_81 = l_System_FilePath_withExtension(x_78, x_80);
x_127 = l_System_Platform_isOSX;
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_128 = l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__2;
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_78);
lean_ctor_set(x_129, 1, x_128);
x_130 = l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__3;
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
x_132 = lean_array_mk(x_131);
x_82 = x_132;
goto block_126;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_133 = l_Lake_buildLeanSharedLibOfStatic___lambda__3___closed__4;
x_134 = lean_string_append(x_133, x_78);
lean_dec(x_78);
x_135 = l_Lake_BuildMetadata_fromJson_x3f___closed__1;
x_136 = lean_string_append(x_134, x_135);
x_137 = lean_box(0);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
x_139 = lean_array_mk(x_138);
x_82 = x_139;
goto block_126;
}
block_126:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; 
x_83 = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLibOfStatic___lambda__2___boxed), 9, 5);
lean_closure_set(x_83, 0, x_1);
lean_closure_set(x_83, 1, x_82);
lean_closure_set(x_83, 2, x_2);
lean_closure_set(x_83, 3, x_81);
lean_closure_set(x_83, 4, x_79);
x_84 = l_Lake_buildLeanO___lambda__4___closed__1;
x_85 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lake_buildFileUnlessUpToDate___spec__1___rarg), 5, 2);
lean_closure_set(x_85, 0, x_84);
lean_closure_set(x_85, 1, x_83);
x_86 = 1;
lean_inc(x_3);
x_87 = l_IO_FS_withIsolatedStreams___at_Lake_buildFileAfterDep___spec__1(x_85, x_86, x_3, x_7, x_5);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_dec(x_88);
x_92 = lean_ctor_get(x_89, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_89, 1);
lean_inc(x_93);
lean_dec(x_89);
x_94 = lean_string_utf8_byte_size(x_92);
x_95 = lean_unsigned_to_nat(0u);
x_96 = lean_nat_dec_eq(x_94, x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_97 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_92, x_94, x_95);
x_98 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_92, x_97, x_94);
x_99 = lean_string_utf8_extract(x_92, x_97, x_98);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_92);
x_100 = l_Lake_buildFileAfterDep___rarg___lambda__3___closed__1;
x_101 = lean_string_append(x_100, x_99);
lean_dec(x_99);
x_102 = l_Lake_BuildMetadata_fromJson_x3f___closed__1;
x_103 = lean_string_append(x_101, x_102);
x_104 = 1;
x_105 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set_uint8(x_105, sizeof(void*)*1, x_104);
x_106 = lean_ctor_get(x_91, 0);
lean_inc(x_106);
x_107 = lean_ctor_get_uint8(x_91, sizeof(void*)*1);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_108 = x_91;
} else {
 lean_dec_ref(x_91);
 x_108 = lean_box(0);
}
x_109 = lean_array_push(x_106, x_105);
if (lean_is_scalar(x_108)) {
 x_110 = lean_alloc_ctor(0, 1, 1);
} else {
 x_110 = x_108;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set_uint8(x_110, sizeof(void*)*1, x_107);
x_111 = lean_box(0);
x_112 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_93, x_111, x_3, x_110, x_90);
lean_dec(x_3);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_94);
lean_dec(x_92);
x_113 = lean_box(0);
x_114 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_93, x_113, x_3, x_91, x_90);
lean_dec(x_3);
return x_114;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_3);
x_115 = lean_ctor_get(x_87, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_116 = x_87;
} else {
 lean_dec_ref(x_87);
 x_116 = lean_box(0);
}
x_117 = lean_ctor_get(x_88, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_88, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_119 = x_88;
} else {
 lean_dec_ref(x_88);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
if (lean_is_scalar(x_116)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_116;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_115);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_3);
x_122 = lean_ctor_get(x_87, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_87, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_124 = x_87;
} else {
 lean_dec_ref(x_87);
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
}
else
{
uint8_t x_140; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_140 = !lean_is_exclusive(x_4);
if (x_140 == 0)
{
lean_object* x_141; 
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_4);
lean_ctor_set(x_141, 1, x_5);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_142 = lean_ctor_get(x_4, 0);
x_143 = lean_ctor_get(x_4, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_4);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_5);
return x_145;
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
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
x_24 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_25 = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLibOfStatic___lambda__3), 5, 3);
lean_closure_set(x_25, 0, x_3);
lean_closure_set(x_25, 1, x_2);
lean_closure_set(x_25, 2, x_4);
x_26 = l_Task_Priority_default;
x_27 = 0;
x_28 = lean_io_map_task(x_25, x_22, x_26, x_27, x_5);
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
x_32 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_23);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_24);
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
lean_dec(x_23);
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
lean_dec(x_3);
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
x_1 = lean_mk_string_unchecked("shared library `", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lake_computeDynlibOfShared___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` has no file name", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lake_computeDynlibOfShared___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lib", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_computeDynlibOfShared___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_computeDynlibOfShared___lambda__2___closed__3;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_computeDynlibOfShared___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_computeDynlibOfShared___lambda__2___closed__3;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_computeDynlibOfShared___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_computeDynlibOfShared___lambda__2___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lake_computeDynlibOfShared___lambda__2___closed__5;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_computeDynlibOfShared___lambda__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` does not start with `lib`; this is not supported on Unix", 58, 58);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_computeDynlibOfShared___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_57; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_4);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_4, 0);
x_59 = lean_ctor_get(x_4, 1);
lean_inc(x_58);
x_60 = l_System_FilePath_fileStem(x_58);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_free_object(x_4);
lean_dec(x_59);
x_61 = l_Lake_computeDynlibOfShared___lambda__2___closed__1;
x_62 = lean_string_append(x_61, x_58);
lean_dec(x_58);
x_63 = l_Lake_computeDynlibOfShared___lambda__2___closed__2;
x_64 = lean_string_append(x_62, x_63);
x_65 = lean_alloc_closure((void*)(l_Lake_computeDynlibOfShared___lambda__1___boxed), 4, 1);
lean_closure_set(x_65, 0, x_64);
x_6 = x_65;
goto block_56;
}
else
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_60, 0);
lean_inc(x_66);
lean_dec(x_60);
x_67 = l_System_Platform_isWindows;
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_68 = lean_string_utf8_byte_size(x_66);
x_69 = lean_unsigned_to_nat(0u);
lean_inc(x_68);
lean_inc(x_66);
x_70 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_70, 0, x_66);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_70, 2, x_68);
x_71 = l_Lake_computeDynlibOfShared___lambda__2___closed__4;
x_72 = l_Substring_nextn(x_70, x_71, x_69);
x_73 = lean_nat_add(x_69, x_72);
lean_dec(x_72);
lean_inc(x_66);
x_74 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_74, 0, x_66);
lean_ctor_set(x_74, 1, x_69);
lean_ctor_set(x_74, 2, x_73);
x_75 = l_Lake_computeDynlibOfShared___lambda__2___closed__6;
x_76 = l_Substring_beq(x_74, x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_66);
lean_free_object(x_4);
lean_dec(x_59);
x_77 = l_Lake_computeDynlibOfShared___lambda__2___closed__1;
x_78 = lean_string_append(x_77, x_58);
lean_dec(x_58);
x_79 = l_Lake_computeDynlibOfShared___lambda__2___closed__7;
x_80 = lean_string_append(x_78, x_79);
x_81 = lean_alloc_closure((void*)(l_Lake_computeDynlibOfShared___lambda__1___boxed), 4, 1);
lean_closure_set(x_81, 0, x_80);
x_6 = x_81;
goto block_56;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_82 = lean_unsigned_to_nat(3u);
x_83 = l_Substring_nextn(x_70, x_82, x_69);
lean_dec(x_70);
x_84 = lean_nat_add(x_69, x_83);
lean_dec(x_83);
x_85 = lean_string_utf8_extract(x_66, x_84, x_68);
lean_dec(x_68);
lean_dec(x_84);
lean_dec(x_66);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_58);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set(x_4, 0, x_86);
x_87 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lake_buildStaticLib___spec__1___rarg___boxed), 4, 1);
lean_closure_set(x_87, 0, x_4);
x_6 = x_87;
goto block_56;
}
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_58);
lean_ctor_set(x_88, 1, x_66);
lean_ctor_set(x_4, 0, x_88);
x_89 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lake_buildStaticLib___spec__1___rarg___boxed), 4, 1);
lean_closure_set(x_89, 0, x_4);
x_6 = x_89;
goto block_56;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_4, 0);
x_91 = lean_ctor_get(x_4, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_4);
lean_inc(x_90);
x_92 = l_System_FilePath_fileStem(x_90);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_91);
x_93 = l_Lake_computeDynlibOfShared___lambda__2___closed__1;
x_94 = lean_string_append(x_93, x_90);
lean_dec(x_90);
x_95 = l_Lake_computeDynlibOfShared___lambda__2___closed__2;
x_96 = lean_string_append(x_94, x_95);
x_97 = lean_alloc_closure((void*)(l_Lake_computeDynlibOfShared___lambda__1___boxed), 4, 1);
lean_closure_set(x_97, 0, x_96);
x_6 = x_97;
goto block_56;
}
else
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_92, 0);
lean_inc(x_98);
lean_dec(x_92);
x_99 = l_System_Platform_isWindows;
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_100 = lean_string_utf8_byte_size(x_98);
x_101 = lean_unsigned_to_nat(0u);
lean_inc(x_100);
lean_inc(x_98);
x_102 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_102, 0, x_98);
lean_ctor_set(x_102, 1, x_101);
lean_ctor_set(x_102, 2, x_100);
x_103 = l_Lake_computeDynlibOfShared___lambda__2___closed__4;
x_104 = l_Substring_nextn(x_102, x_103, x_101);
x_105 = lean_nat_add(x_101, x_104);
lean_dec(x_104);
lean_inc(x_98);
x_106 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_106, 0, x_98);
lean_ctor_set(x_106, 1, x_101);
lean_ctor_set(x_106, 2, x_105);
x_107 = l_Lake_computeDynlibOfShared___lambda__2___closed__6;
x_108 = l_Substring_beq(x_106, x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_102);
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_91);
x_109 = l_Lake_computeDynlibOfShared___lambda__2___closed__1;
x_110 = lean_string_append(x_109, x_90);
lean_dec(x_90);
x_111 = l_Lake_computeDynlibOfShared___lambda__2___closed__7;
x_112 = lean_string_append(x_110, x_111);
x_113 = lean_alloc_closure((void*)(l_Lake_computeDynlibOfShared___lambda__1___boxed), 4, 1);
lean_closure_set(x_113, 0, x_112);
x_6 = x_113;
goto block_56;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_114 = lean_unsigned_to_nat(3u);
x_115 = l_Substring_nextn(x_102, x_114, x_101);
lean_dec(x_102);
x_116 = lean_nat_add(x_101, x_115);
lean_dec(x_115);
x_117 = lean_string_utf8_extract(x_98, x_116, x_100);
lean_dec(x_100);
lean_dec(x_116);
lean_dec(x_98);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_90);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_91);
x_120 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lake_buildStaticLib___spec__1___rarg___boxed), 4, 1);
lean_closure_set(x_120, 0, x_119);
x_6 = x_120;
goto block_56;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_90);
lean_ctor_set(x_121, 1, x_98);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_91);
x_123 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lake_buildStaticLib___spec__1___rarg___boxed), 4, 1);
lean_closure_set(x_123, 0, x_122);
x_6 = x_123;
goto block_56;
}
}
}
block_56:
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
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
x_15 = lean_string_utf8_byte_size(x_13);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; 
x_18 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_13, x_15, x_16);
x_19 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_13, x_18, x_15);
x_20 = lean_string_utf8_extract(x_13, x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_13);
x_21 = l_Lake_buildFileAfterDep___rarg___lambda__3___closed__1;
x_22 = lean_string_append(x_21, x_20);
lean_dec(x_20);
x_23 = l_Lake_BuildMetadata_fromJson_x3f___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = 1;
x_26 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_25);
x_27 = !lean_is_exclusive(x_12);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_12, 0);
x_29 = lean_array_push(x_28, x_26);
lean_ctor_set(x_12, 0, x_29);
x_30 = lean_box(0);
x_31 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_14, x_30, x_1, x_12, x_11);
lean_dec(x_1);
return x_31;
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_12, 0);
x_33 = lean_ctor_get_uint8(x_12, sizeof(void*)*1);
lean_inc(x_32);
lean_dec(x_12);
x_34 = lean_array_push(x_32, x_26);
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_33);
x_36 = lean_box(0);
x_37 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_14, x_36, x_1, x_35, x_11);
lean_dec(x_1);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_15);
lean_dec(x_13);
x_38 = lean_box(0);
x_39 = l_Lake_buildFileAfterDep___rarg___lambda__2(x_14, x_38, x_1, x_12, x_11);
lean_dec(x_1);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_8);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_8, 0);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_9);
if (x_42 == 0)
{
return x_8;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_9, 0);
x_44 = lean_ctor_get(x_9, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_9);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_8, 0, x_45);
return x_8;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_8, 1);
lean_inc(x_46);
lean_dec(x_8);
x_47 = lean_ctor_get(x_9, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_9, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_49 = x_9;
} else {
 lean_dec_ref(x_9);
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
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_8);
if (x_52 == 0)
{
return x_8;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_8, 0);
x_54 = lean_ctor_get(x_8, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_8);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_2);
if (x_124 == 0)
{
lean_object* x_125; 
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_2);
lean_ctor_set(x_125, 1, x_3);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_126 = lean_ctor_get(x_2, 0);
x_127 = lean_ctor_get(x_2, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_2);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_3);
return x_129;
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
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_23 = lean_alloc_closure((void*)(l_Lake_computeDynlibOfShared___lambda__2), 3, 1);
lean_closure_set(x_23, 0, x_2);
x_24 = l_Task_Priority_default;
x_25 = 0;
x_26 = lean_io_map_task(x_23, x_20, x_24, x_25, x_3);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
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
x_30 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_21);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_22);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_21);
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_34 = x_26;
} else {
 lean_dec_ref(x_26);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
return x_35;
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
lean_object* initialize_Lake_Config_Monad(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Actions(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_JsonObject(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Common(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Monad(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Actions(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_JsonObject(builtin, lean_io_mk_world());
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
l_Lake_BuildMetadata_fromJson_x3f___closed__9 = _init_l_Lake_BuildMetadata_fromJson_x3f___closed__9();
lean_mark_persistent(l_Lake_BuildMetadata_fromJson_x3f___closed__9);
l_Lake_BuildMetadata_fromJson_x3f___closed__10 = _init_l_Lake_BuildMetadata_fromJson_x3f___closed__10();
lean_mark_persistent(l_Lake_BuildMetadata_fromJson_x3f___closed__10);
l_Lake_BuildMetadata_fromJson_x3f___closed__11 = _init_l_Lake_BuildMetadata_fromJson_x3f___closed__11();
lean_mark_persistent(l_Lake_BuildMetadata_fromJson_x3f___closed__11);
l_Lake_BuildMetadata_fromJson_x3f___closed__12 = _init_l_Lake_BuildMetadata_fromJson_x3f___closed__12();
lean_mark_persistent(l_Lake_BuildMetadata_fromJson_x3f___closed__12);
l_Lake_BuildMetadata_fromJson_x3f___closed__13 = _init_l_Lake_BuildMetadata_fromJson_x3f___closed__13();
lean_mark_persistent(l_Lake_BuildMetadata_fromJson_x3f___closed__13);
l_Lake_BuildMetadata_fromJson_x3f___closed__14 = _init_l_Lake_BuildMetadata_fromJson_x3f___closed__14();
lean_mark_persistent(l_Lake_BuildMetadata_fromJson_x3f___closed__14);
l_Lake_BuildMetadata_fromJson_x3f___closed__15 = _init_l_Lake_BuildMetadata_fromJson_x3f___closed__15();
lean_mark_persistent(l_Lake_BuildMetadata_fromJson_x3f___closed__15);
l_Lake_BuildMetadata_fromJson_x3f___closed__16 = _init_l_Lake_BuildMetadata_fromJson_x3f___closed__16();
lean_mark_persistent(l_Lake_BuildMetadata_fromJson_x3f___closed__16);
l_Lake_BuildMetadata_fromJson_x3f___closed__17 = _init_l_Lake_BuildMetadata_fromJson_x3f___closed__17();
lean_mark_persistent(l_Lake_BuildMetadata_fromJson_x3f___closed__17);
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
l_Lake_buildUnlessUpToDate_x3f_go___closed__1 = _init_l_Lake_buildUnlessUpToDate_x3f_go___closed__1();
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
l_Lake_buildO___lambda__1___closed__3 = _init_l_Lake_buildO___lambda__1___closed__3();
l_Lake_buildO___lambda__1___closed__4___boxed__const__1 = _init_l_Lake_buildO___lambda__1___closed__4___boxed__const__1();
lean_mark_persistent(l_Lake_buildO___lambda__1___closed__4___boxed__const__1);
l_Lake_buildO___lambda__1___closed__4 = _init_l_Lake_buildO___lambda__1___closed__4();
lean_mark_persistent(l_Lake_buildO___lambda__1___closed__4);
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
l_Lake_computeDynlibOfShared___lambda__2___closed__1 = _init_l_Lake_computeDynlibOfShared___lambda__2___closed__1();
lean_mark_persistent(l_Lake_computeDynlibOfShared___lambda__2___closed__1);
l_Lake_computeDynlibOfShared___lambda__2___closed__2 = _init_l_Lake_computeDynlibOfShared___lambda__2___closed__2();
lean_mark_persistent(l_Lake_computeDynlibOfShared___lambda__2___closed__2);
l_Lake_computeDynlibOfShared___lambda__2___closed__3 = _init_l_Lake_computeDynlibOfShared___lambda__2___closed__3();
lean_mark_persistent(l_Lake_computeDynlibOfShared___lambda__2___closed__3);
l_Lake_computeDynlibOfShared___lambda__2___closed__4 = _init_l_Lake_computeDynlibOfShared___lambda__2___closed__4();
lean_mark_persistent(l_Lake_computeDynlibOfShared___lambda__2___closed__4);
l_Lake_computeDynlibOfShared___lambda__2___closed__5 = _init_l_Lake_computeDynlibOfShared___lambda__2___closed__5();
lean_mark_persistent(l_Lake_computeDynlibOfShared___lambda__2___closed__5);
l_Lake_computeDynlibOfShared___lambda__2___closed__6 = _init_l_Lake_computeDynlibOfShared___lambda__2___closed__6();
lean_mark_persistent(l_Lake_computeDynlibOfShared___lambda__2___closed__6);
l_Lake_computeDynlibOfShared___lambda__2___closed__7 = _init_l_Lake_computeDynlibOfShared___lambda__2___closed__7();
lean_mark_persistent(l_Lake_computeDynlibOfShared___lambda__2___closed__7);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

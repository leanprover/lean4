// Lean compiler output
// Module: Lake.Build.Library
// Imports: Lake.Build.Common Lake.Build.Targets
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Package_fetchTargetJob(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_LeanLib_defaultFacet;
LEAN_EXPORT lean_object* l_Lake_LeanLib_initFacetConfigs;
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_LeanLib_sharedFacetConfig___spec__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_LeanLib_recBuildShared___spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_modulesFacetConfig___closed__2;
static lean_object* l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__4;
lean_object* l_Lean_Json_compress(lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__1;
static lean_object* l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__1;
static lean_object* l_Lake_LeanLib_sharedFacetConfig___closed__3;
static lean_object* l_Lake_LeanLib_modulesFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig;
lean_object* l_Lake_nameToSharedLib(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_sharedFacetConfig;
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__4;
static lean_object* l_Lake_LeanLib_staticExportFacetConfig___closed__1;
lean_object* l_Lake_instBEqModule___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_sharedFacetConfig___closed__2;
static lean_object* l_Lake_LeanLib_staticFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stdout(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lake_Target_fetchIn___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___at_Lake_LeanLib_recBuildShared___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___spec__2___lambda__1(lean_object*);
uint8_t l_Lean_RBNode_isRed___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_defaultFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_Lake_LeanLib_modulesFacet;
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_LeanLib_recCollectLocalModules___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_LeanLib_getModuleArray(lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__2;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__10(lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lake_Job_mix___rarg(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_staticFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildDefaultFacets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_ExternLib_dynlibFacet;
extern lean_object* l_Lake_Package_keyword;
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_LeanLib_recCollectLocalModules___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_LeanLib_recBuildShared___spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lambda__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLib_recBuildShared___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_renew___rarg(lean_object*);
lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_extraDepFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildExtraDepTargets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Module_transImportsFacet;
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at_Lake_LeanLib_recBuildShared___spec__8___boxed(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__15(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_LeanLib_extraDepFacet;
static lean_object* l_Lake_OrdHashSet_insert___at_Lake_LeanLib_recBuildShared___spec__9___closed__1;
lean_object* l_Lake_buildStaticLib(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at_Lake_LeanLib_recBuildShared___spec__8(lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_recBuildShared___closed__1;
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__3;
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__5;
lean_object* l_Lake_buildLeanSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___spec__2___lambda__1___boxed(lean_object*);
static lean_object* l_Lake_OrdHashSet_insert___at_Lake_LeanLib_recBuildShared___spec__9___closed__2;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at_Lake_LeanLib_recBuildShared___spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_recBuildStatic___closed__6;
lean_object* l_Lake_instHashableModule___boxed(lean_object*);
lean_object* lean_task_pure(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_modulesFacetConfig;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__12___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__1;
lean_object* l_Lean_RBNode_setBlack___rarg(lean_object*);
lean_object* l_Lake_Job_mixArray___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__13(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLib_modulesFacetConfig___spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_recCollectLocalModules___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_LeanLib_leanArtsFacet;
lean_object* l_Lake_nullFormat___rarg___boxed(lean_object*, lean_object*);
extern lean_object* l_Lake_instDataKindUnit;
extern lean_object* l_Lake_Module_leanArtsFacet;
lean_object* l_Lake_BuildInfo_fetch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__5;
static lean_object* l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildLean___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLib_modulesFacetConfig___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_withRegisterJob___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_LeanLib_staticFacetConfig___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_recBuildStatic___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Lake_initLibraryFacetConfigs;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_recCollectLocalModules___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_instDataKindFilePath;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildLean(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLib_recBuildShared___spec__14(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at_Lake_LeanLib_recBuildShared___spec__9(lean_object*, lean_object*);
lean_object* l_Lake_PartialBuildKey_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_LeanLib_staticFacetConfig___spec__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_LeanLib_recCollectLocalModules_go___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_String_fromUTF8_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lake_LeanLib_recCollectLocalModules_go___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_LeanLib_recCollectLocalModules___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildLean___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Task_Priority_default;
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_recBuildStatic___closed__4;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__11(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__3;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__2;
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
lean_object* l_Lake_EquipT_instMonad___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacetConfig;
static lean_object* l_Lake_LeanLib_recCollectLocalModules___closed__1;
extern lean_object* l_instMonadBaseIO;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__6;
extern lean_object* l_Lake_LeanLib_staticFacet;
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_BuildTrace_nil;
static lean_object* l_Lake_LeanLib_recBuildStatic___closed__5;
lean_object* lean_get_set_stderr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_ModuleFacet_fetch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_LeanLib_recCollectLocalModules_go___spec__5___at_Lake_LeanLib_recCollectLocalModules_go___spec__6(lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_modulesFacetConfig___closed__3;
static lean_object* l_Lake_LeanLib_recBuildLean___closed__2;
static lean_object* l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* l_Lake_Job_toOpaque___rarg(lean_object*);
static lean_object* l_Lake_LeanLib_leanArtsFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLib_recBuildDefaultFacets___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recBuildShared___spec__18(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_modulesFacetConfig___closed__5;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lake_LeanLib_recCollectLocalModules_go___spec__4(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__3;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_staticExportFacetConfig___closed__2;
static lean_object* l_Lake_LeanLib_leanArtsFacetConfig___closed__1;
lean_object* l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_LeanLib_staticExportFacet;
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_JobResult_prependLog___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lake_LeanLib_initFacetConfigs___spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_modulesFacetConfig___closed__4;
static lean_object* l_Lake_LeanLib_recCollectLocalModules_go___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recBuildShared___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_instDecidableEqVerbosity(uint8_t, uint8_t);
static lean_object* l_Lake_LeanLib_recBuildStatic___lambda__4___closed__3;
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lake_LeanLib_initFacetConfigs___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lake_LeanLib_recCollectLocalModules_go___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_Lake_Package_extraDepFacet;
static lean_object* l_Lake_LeanLib_recBuildLean___closed__3;
extern lean_object* l_Lean_NameSet_empty;
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildExtraDepTargets___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
lean_object* l_Array_mapMUnsafe_map___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2;
lean_object* l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___spec__2(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lake_EquipT_bind___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_defaultFacetConfig;
lean_object* l_Array_shrink___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___at_Lake_LeanLib_recBuildShared___spec__16(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_Lake_instDataKindDynlib;
static lean_object* l_Lake_LeanLib_extraDepFacetConfig___closed__1;
static lean_object* l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__2;
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_LeanLib_recBuildShared___spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
lean_object* l_Substring_prevn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
static lean_object* l_Lake_LeanLib_recBuildStatic___closed__2;
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lambda__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_recCollectLocalModules_go___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_recBuildStatic___closed__3;
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lake_mkRelPathString(lean_object*);
extern lean_object* l_Lake_Module_importsFacet;
static lean_object* l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__6;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_get_set_stdin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildShared___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_sharedFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildShared___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig;
lean_object* l_Lake_nameToStaticLib(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_recCollectLocalModules_go___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLib_recBuildDefaultFacets___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildExtraDepTargets___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_LeanLib_recCollectLocalModules_go___spec__3(lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_LeanLib_recCollectLocalModules___spec__2(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lake_LeanLib_recBuildStatic___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
extern lean_object* l_Lake_Module_keyword;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_recBuildStatic___closed__7;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_recBuildLean___closed__4;
lean_object* lean_io_wait(lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_leanArtsFacetConfig___closed__3;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__1;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLib_staticFacetConfig___closed__3;
lean_object* l_Lake_EStateT_instMonad___rarg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_LeanLib_extraDepFacetConfig;
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildExtraDepTargets___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_LeanLib_sharedFacetConfig___spec__1___boxed(lean_object*, lean_object*);
extern lean_object* l_Lake_LeanLib_sharedFacet;
extern uint8_t l_System_Platform_isWindows;
static lean_object* l_Lake_LeanLib_recBuildLean___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lake_ExternLib_keyword;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildExtraDepTargets___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__5;
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_LeanLib_recCollectLocalModules___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__4;
static lean_object* l_Lake_LeanLib_defaultFacetConfig___closed__1;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lake_LeanLib_recCollectLocalModules_go___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_4, 2);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_name_eq(x_6, x_7);
if (x_8 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_recCollectLocalModules_go___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_37; 
x_37 = lean_usize_dec_lt(x_6, x_5);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_7);
lean_ctor_set(x_38, 1, x_12);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_13);
return x_39;
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_array_uget(x_4, x_6);
x_41 = !lean_is_exclusive(x_7);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_42 = lean_ctor_get(x_7, 0);
x_43 = lean_ctor_get(x_7, 1);
x_44 = lean_ctor_get(x_40, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get(x_1, 1);
x_47 = lean_name_eq(x_45, x_46);
lean_dec(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_40);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_7);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_12);
x_14 = x_49;
x_15 = x_13;
goto block_36;
}
else
{
lean_object* x_50; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_50 = l_Lake_LeanLib_recCollectLocalModules_go(x_1, x_40, x_43, x_42, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = !lean_is_exclusive(x_51);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_51, 0);
lean_dec(x_55);
x_56 = lean_ctor_get(x_52, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
lean_dec(x_52);
lean_ctor_set(x_7, 1, x_56);
lean_ctor_set(x_7, 0, x_57);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_7);
lean_ctor_set(x_51, 0, x_58);
x_14 = x_51;
x_15 = x_53;
goto block_36;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_51, 1);
lean_inc(x_59);
lean_dec(x_51);
x_60 = lean_ctor_get(x_52, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_52, 1);
lean_inc(x_61);
lean_dec(x_52);
lean_ctor_set(x_7, 1, x_60);
lean_ctor_set(x_7, 0, x_61);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_7);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_59);
x_14 = x_63;
x_15 = x_53;
goto block_36;
}
}
else
{
lean_object* x_64; uint8_t x_65; 
lean_free_object(x_7);
x_64 = lean_ctor_get(x_50, 1);
lean_inc(x_64);
lean_dec(x_50);
x_65 = !lean_is_exclusive(x_51);
if (x_65 == 0)
{
x_14 = x_51;
x_15 = x_64;
goto block_36;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_51, 0);
x_67 = lean_ctor_get(x_51, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_51);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_14 = x_68;
x_15 = x_64;
goto block_36;
}
}
}
else
{
uint8_t x_69; 
lean_free_object(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_69 = !lean_is_exclusive(x_50);
if (x_69 == 0)
{
return x_50;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_50, 0);
x_71 = lean_ctor_get(x_50, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_50);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_73 = lean_ctor_get(x_7, 0);
x_74 = lean_ctor_get(x_7, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_7);
x_75 = lean_ctor_get(x_40, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_ctor_get(x_1, 1);
x_78 = lean_name_eq(x_76, x_77);
lean_dec(x_76);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_40);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_73);
lean_ctor_set(x_79, 1, x_74);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_12);
x_14 = x_81;
x_15 = x_13;
goto block_36;
}
else
{
lean_object* x_82; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_82 = l_Lake_LeanLib_recCollectLocalModules_go(x_1, x_40, x_74, x_73, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_87 = x_83;
} else {
 lean_dec_ref(x_83);
 x_87 = lean_box(0);
}
x_88 = lean_ctor_get(x_84, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_84, 1);
lean_inc(x_89);
lean_dec(x_84);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
if (lean_is_scalar(x_87)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_87;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_86);
x_14 = x_92;
x_15 = x_85;
goto block_36;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_82, 1);
lean_inc(x_93);
lean_dec(x_82);
x_94 = lean_ctor_get(x_83, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_83, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_96 = x_83;
} else {
 lean_dec_ref(x_83);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
x_14 = x_97;
x_15 = x_93;
goto block_36;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_98 = lean_ctor_get(x_82, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_82, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_100 = x_82;
} else {
 lean_dec_ref(x_82);
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
}
block_36:
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_19);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_15);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; 
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_ctor_get(x_16, 0);
lean_inc(x_26);
lean_dec(x_16);
x_27 = 1;
x_28 = lean_usize_add(x_6, x_27);
x_6 = x_28;
x_7 = x_26;
x_12 = x_25;
x_13 = x_15;
goto _start;
}
}
else
{
uint8_t x_30; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_30 = !lean_is_exclusive(x_14);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_14);
lean_ctor_set(x_31, 1, x_15);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_14, 0);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_14);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_15);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_LeanLib_recCollectLocalModules_go___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_LeanLib_recCollectLocalModules_go___spec__5___at_Lake_LeanLib_recCollectLocalModules_go___spec__6(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = l_Lean_Name_hash___override(x_7);
lean_dec(x_7);
x_9 = 32;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; size_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get(x_2, 2);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_2);
x_26 = lean_array_get_size(x_1);
x_27 = lean_ctor_get(x_23, 2);
lean_inc(x_27);
x_28 = l_Lean_Name_hash___override(x_27);
lean_dec(x_27);
x_29 = 32;
x_30 = lean_uint64_shift_right(x_28, x_29);
x_31 = lean_uint64_xor(x_28, x_30);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lake_LeanLib_recCollectLocalModules_go___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_LeanLib_recCollectLocalModules_go___spec__5___at_Lake_LeanLib_recCollectLocalModules_go___spec__6(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_LeanLib_recCollectLocalModules_go___spec__3(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lake_LeanLib_recCollectLocalModules_go___spec__4(x_7, x_1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
static lean_object* _init_l_Lake_LeanLib_recCollectLocalModules_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_recCollectLocalModules_go___lambda__1___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; size_t x_23; size_t x_24; size_t x_25; size_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_11 = l_Lake_LeanLib_recCollectLocalModules_go___closed__1;
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
x_14 = lean_array_get_size(x_13);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
x_16 = l_Lean_Name_hash___override(x_15);
x_17 = 32;
x_18 = lean_uint64_shift_right(x_16, x_17);
x_19 = lean_uint64_xor(x_16, x_18);
x_20 = 16;
x_21 = lean_uint64_shift_right(x_19, x_20);
x_22 = lean_uint64_xor(x_19, x_21);
x_23 = lean_uint64_to_usize(x_22);
x_24 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_25 = 1;
x_26 = lean_usize_sub(x_24, x_25);
x_27 = lean_usize_land(x_23, x_26);
x_28 = lean_array_uget(x_13, x_27);
x_29 = l_Std_DHashMap_Internal_AssocList_contains___at_Lake_LeanLib_recCollectLocalModules_go___spec__1(x_2, x_28);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_4);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; 
x_31 = lean_ctor_get(x_4, 1);
lean_dec(x_31);
x_32 = lean_ctor_get(x_4, 0);
lean_dec(x_32);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_15);
x_34 = l_Lake_Module_keyword;
x_35 = l_Lake_Module_importsFacet;
lean_inc(x_2);
x_36 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_2);
lean_ctor_set(x_36, 3, x_35);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_37 = lean_apply_6(x_5, x_36, x_6, x_7, x_8, x_9, x_10);
x_224 = lean_unsigned_to_nat(1u);
x_225 = lean_nat_add(x_12, x_224);
lean_dec(x_12);
x_226 = lean_box(0);
lean_inc(x_2);
x_227 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_227, 0, x_2);
lean_ctor_set(x_227, 1, x_226);
lean_ctor_set(x_227, 2, x_28);
x_228 = lean_array_uset(x_13, x_27, x_227);
x_229 = lean_unsigned_to_nat(4u);
x_230 = lean_nat_mul(x_225, x_229);
x_231 = lean_unsigned_to_nat(3u);
x_232 = lean_nat_div(x_230, x_231);
lean_dec(x_230);
x_233 = lean_array_get_size(x_228);
x_234 = lean_nat_dec_le(x_232, x_233);
lean_dec(x_233);
lean_dec(x_232);
if (x_234 == 0)
{
lean_object* x_235; 
x_235 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_LeanLib_recCollectLocalModules_go___spec__3(x_228);
lean_ctor_set(x_4, 1, x_235);
lean_ctor_set(x_4, 0, x_225);
x_38 = x_4;
goto block_223;
}
else
{
lean_ctor_set(x_4, 1, x_228);
lean_ctor_set(x_4, 0, x_225);
x_38 = x_4;
goto block_223;
}
block_223:
{
lean_object* x_39; lean_object* x_40; lean_object* x_80; lean_object* x_81; lean_object* x_97; lean_object* x_98; 
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_122; 
x_122 = lean_ctor_get(x_37, 0);
lean_inc(x_122);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_123 = lean_ctor_get(x_37, 1);
lean_inc(x_123);
lean_dec(x_37);
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_125);
lean_dec(x_122);
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
lean_dec(x_124);
x_127 = lean_io_wait(x_126, x_123);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_dec(x_127);
x_131 = !lean_is_exclusive(x_128);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_132 = lean_ctor_get(x_128, 0);
x_133 = lean_ctor_get(x_128, 1);
lean_dec(x_133);
x_134 = lean_ctor_get(x_129, 0);
lean_inc(x_134);
lean_dec(x_129);
x_135 = lean_array_get_size(x_134);
x_136 = lean_unsigned_to_nat(0u);
x_137 = lean_nat_dec_lt(x_136, x_135);
if (x_137 == 0)
{
lean_dec(x_135);
lean_dec(x_134);
lean_ctor_set(x_128, 1, x_125);
x_97 = x_128;
x_98 = x_130;
goto block_121;
}
else
{
uint8_t x_138; 
x_138 = lean_nat_dec_le(x_135, x_135);
if (x_138 == 0)
{
lean_dec(x_135);
lean_dec(x_134);
lean_ctor_set(x_128, 1, x_125);
x_97 = x_128;
x_98 = x_130;
goto block_121;
}
else
{
size_t x_139; size_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
lean_free_object(x_128);
x_139 = 0;
x_140 = lean_usize_of_nat(x_135);
lean_dec(x_135);
x_141 = lean_box(0);
x_142 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_134, x_139, x_140, x_141, x_125, x_130);
lean_dec(x_134);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = !lean_is_exclusive(x_143);
if (x_145 == 0)
{
lean_object* x_146; 
x_146 = lean_ctor_get(x_143, 0);
lean_dec(x_146);
lean_ctor_set(x_143, 0, x_132);
x_97 = x_143;
x_98 = x_144;
goto block_121;
}
else
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_143, 1);
lean_inc(x_147);
lean_dec(x_143);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_132);
lean_ctor_set(x_148, 1, x_147);
x_97 = x_148;
x_98 = x_144;
goto block_121;
}
}
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_149 = lean_ctor_get(x_128, 0);
lean_inc(x_149);
lean_dec(x_128);
x_150 = lean_ctor_get(x_129, 0);
lean_inc(x_150);
lean_dec(x_129);
x_151 = lean_array_get_size(x_150);
x_152 = lean_unsigned_to_nat(0u);
x_153 = lean_nat_dec_lt(x_152, x_151);
if (x_153 == 0)
{
lean_object* x_154; 
lean_dec(x_151);
lean_dec(x_150);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_149);
lean_ctor_set(x_154, 1, x_125);
x_97 = x_154;
x_98 = x_130;
goto block_121;
}
else
{
uint8_t x_155; 
x_155 = lean_nat_dec_le(x_151, x_151);
if (x_155 == 0)
{
lean_object* x_156; 
lean_dec(x_151);
lean_dec(x_150);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_149);
lean_ctor_set(x_156, 1, x_125);
x_97 = x_156;
x_98 = x_130;
goto block_121;
}
else
{
size_t x_157; size_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_157 = 0;
x_158 = lean_usize_of_nat(x_151);
lean_dec(x_151);
x_159 = lean_box(0);
x_160 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_150, x_157, x_158, x_159, x_125, x_130);
lean_dec(x_150);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
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
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_149);
lean_ctor_set(x_165, 1, x_163);
x_97 = x_165;
x_98 = x_162;
goto block_121;
}
}
}
}
else
{
lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_166 = lean_ctor_get(x_128, 1);
lean_inc(x_166);
x_167 = lean_ctor_get(x_127, 1);
lean_inc(x_167);
lean_dec(x_127);
x_168 = !lean_is_exclusive(x_128);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_169 = lean_ctor_get(x_128, 0);
x_170 = lean_ctor_get(x_128, 1);
lean_dec(x_170);
x_171 = lean_ctor_get(x_166, 0);
lean_inc(x_171);
lean_dec(x_166);
x_172 = lean_array_get_size(x_171);
x_173 = lean_unsigned_to_nat(0u);
x_174 = lean_nat_dec_lt(x_173, x_172);
if (x_174 == 0)
{
lean_dec(x_172);
lean_dec(x_171);
lean_ctor_set(x_128, 1, x_125);
x_97 = x_128;
x_98 = x_167;
goto block_121;
}
else
{
uint8_t x_175; 
x_175 = lean_nat_dec_le(x_172, x_172);
if (x_175 == 0)
{
lean_dec(x_172);
lean_dec(x_171);
lean_ctor_set(x_128, 1, x_125);
x_97 = x_128;
x_98 = x_167;
goto block_121;
}
else
{
size_t x_176; size_t x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
lean_free_object(x_128);
x_176 = 0;
x_177 = lean_usize_of_nat(x_172);
lean_dec(x_172);
x_178 = lean_box(0);
x_179 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_171, x_176, x_177, x_178, x_125, x_167);
lean_dec(x_171);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = !lean_is_exclusive(x_180);
if (x_182 == 0)
{
lean_object* x_183; 
x_183 = lean_ctor_get(x_180, 0);
lean_dec(x_183);
lean_ctor_set_tag(x_180, 1);
lean_ctor_set(x_180, 0, x_169);
x_97 = x_180;
x_98 = x_181;
goto block_121;
}
else
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_ctor_get(x_180, 1);
lean_inc(x_184);
lean_dec(x_180);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_169);
lean_ctor_set(x_185, 1, x_184);
x_97 = x_185;
x_98 = x_181;
goto block_121;
}
}
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_186 = lean_ctor_get(x_128, 0);
lean_inc(x_186);
lean_dec(x_128);
x_187 = lean_ctor_get(x_166, 0);
lean_inc(x_187);
lean_dec(x_166);
x_188 = lean_array_get_size(x_187);
x_189 = lean_unsigned_to_nat(0u);
x_190 = lean_nat_dec_lt(x_189, x_188);
if (x_190 == 0)
{
lean_object* x_191; 
lean_dec(x_188);
lean_dec(x_187);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_186);
lean_ctor_set(x_191, 1, x_125);
x_97 = x_191;
x_98 = x_167;
goto block_121;
}
else
{
uint8_t x_192; 
x_192 = lean_nat_dec_le(x_188, x_188);
if (x_192 == 0)
{
lean_object* x_193; 
lean_dec(x_188);
lean_dec(x_187);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_186);
lean_ctor_set(x_193, 1, x_125);
x_97 = x_193;
x_98 = x_167;
goto block_121;
}
else
{
size_t x_194; size_t x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_194 = 0;
x_195 = lean_usize_of_nat(x_188);
lean_dec(x_188);
x_196 = lean_box(0);
x_197 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_187, x_194, x_195, x_196, x_125, x_167);
lean_dec(x_187);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_201 = x_198;
} else {
 lean_dec_ref(x_198);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_202 = x_201;
 lean_ctor_set_tag(x_202, 1);
}
lean_ctor_set(x_202, 0, x_186);
lean_ctor_set(x_202, 1, x_200);
x_97 = x_202;
x_98 = x_199;
goto block_121;
}
}
}
}
}
else
{
uint8_t x_203; 
lean_dec(x_125);
lean_dec(x_38);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_203 = !lean_is_exclusive(x_127);
if (x_203 == 0)
{
return x_127;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_127, 0);
x_205 = lean_ctor_get(x_127, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_127);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
else
{
uint8_t x_207; 
lean_dec(x_38);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_207 = !lean_is_exclusive(x_37);
if (x_207 == 0)
{
lean_object* x_208; uint8_t x_209; 
x_208 = lean_ctor_get(x_37, 0);
lean_dec(x_208);
x_209 = !lean_is_exclusive(x_122);
if (x_209 == 0)
{
return x_37;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_122, 0);
x_211 = lean_ctor_get(x_122, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_122);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
lean_ctor_set(x_37, 0, x_212);
return x_37;
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_213 = lean_ctor_get(x_37, 1);
lean_inc(x_213);
lean_dec(x_37);
x_214 = lean_ctor_get(x_122, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_122, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_216 = x_122;
} else {
 lean_dec_ref(x_122);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(1, 2, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_215);
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_213);
return x_218;
}
}
}
else
{
uint8_t x_219; 
lean_dec(x_38);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_219 = !lean_is_exclusive(x_37);
if (x_219 == 0)
{
return x_37;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_37, 0);
x_221 = lean_ctor_get(x_37, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_37);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
return x_222;
}
}
block_79:
{
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_3);
x_45 = lean_array_size(x_41);
x_46 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_47 = l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_recCollectLocalModules_go___spec__2(x_1, x_41, x_43, x_41, x_45, x_46, x_44, x_5, x_6, x_7, x_8, x_42, x_40);
lean_dec(x_41);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
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
x_54 = lean_array_push(x_53, x_2);
x_55 = lean_box(0);
x_56 = lean_apply_9(x_11, x_52, x_54, x_55, x_5, x_6, x_7, x_8, x_51, x_50);
return x_56;
}
else
{
uint8_t x_57; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_47);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_47, 0);
lean_dec(x_58);
x_59 = !lean_is_exclusive(x_48);
if (x_59 == 0)
{
return x_47;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_48, 0);
x_61 = lean_ctor_get(x_48, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_48);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_47, 0, x_62);
return x_47;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_47, 1);
lean_inc(x_63);
lean_dec(x_47);
x_64 = lean_ctor_get(x_48, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_48, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_66 = x_48;
} else {
 lean_dec_ref(x_48);
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
uint8_t x_69; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_69 = !lean_is_exclusive(x_47);
if (x_69 == 0)
{
return x_47;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_47, 0);
x_71 = lean_ctor_get(x_47, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_47);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_38);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_73 = !lean_is_exclusive(x_39);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_39);
lean_ctor_set(x_74, 1, x_40);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_39, 0);
x_76 = lean_ctor_get(x_39, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_39);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_40);
return x_78;
}
}
}
block_96:
{
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_80);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_80, 1);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec(x_83);
lean_ctor_set(x_80, 1, x_84);
x_39 = x_80;
x_40 = x_81;
goto block_79;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_80, 0);
x_86 = lean_ctor_get(x_80, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_80);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec(x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_87);
x_39 = x_88;
x_40 = x_81;
goto block_79;
}
}
else
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_80);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_80, 1);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
lean_dec(x_90);
lean_ctor_set(x_80, 1, x_91);
x_39 = x_80;
x_40 = x_81;
goto block_79;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_80, 0);
x_93 = lean_ctor_get(x_80, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_80);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
lean_dec(x_93);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_94);
x_39 = x_95;
x_40 = x_81;
goto block_79;
}
}
}
block_121:
{
if (lean_obj_tag(x_97) == 0)
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_97);
if (x_99 == 0)
{
lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_97, 1);
x_101 = 0;
x_102 = l_Lake_BuildTrace_nil;
x_103 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set_uint8(x_103, sizeof(void*)*2, x_101);
lean_ctor_set(x_97, 1, x_103);
x_80 = x_97;
x_81 = x_98;
goto block_96;
}
else
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_104 = lean_ctor_get(x_97, 0);
x_105 = lean_ctor_get(x_97, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_97);
x_106 = 0;
x_107 = l_Lake_BuildTrace_nil;
x_108 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set_uint8(x_108, sizeof(void*)*2, x_106);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_104);
lean_ctor_set(x_109, 1, x_108);
x_80 = x_109;
x_81 = x_98;
goto block_96;
}
}
else
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_97);
if (x_110 == 0)
{
lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_ctor_get(x_97, 1);
x_112 = 0;
x_113 = l_Lake_BuildTrace_nil;
x_114 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_113);
lean_ctor_set_uint8(x_114, sizeof(void*)*2, x_112);
lean_ctor_set(x_97, 1, x_114);
x_80 = x_97;
x_81 = x_98;
goto block_96;
}
else
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_115 = lean_ctor_get(x_97, 0);
x_116 = lean_ctor_get(x_97, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_97);
x_117 = 0;
x_118 = l_Lake_BuildTrace_nil;
x_119 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set_uint8(x_119, sizeof(void*)*2, x_117);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_115);
lean_ctor_set(x_120, 1, x_119);
x_80 = x_120;
x_81 = x_98;
goto block_96;
}
}
}
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; uint8_t x_380; 
lean_dec(x_4);
x_236 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_236, 0, x_15);
x_237 = l_Lake_Module_keyword;
x_238 = l_Lake_Module_importsFacet;
lean_inc(x_2);
x_239 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_239, 0, x_236);
lean_ctor_set(x_239, 1, x_237);
lean_ctor_set(x_239, 2, x_2);
lean_ctor_set(x_239, 3, x_238);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_240 = lean_apply_6(x_5, x_239, x_6, x_7, x_8, x_9, x_10);
x_370 = lean_unsigned_to_nat(1u);
x_371 = lean_nat_add(x_12, x_370);
lean_dec(x_12);
x_372 = lean_box(0);
lean_inc(x_2);
x_373 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_373, 0, x_2);
lean_ctor_set(x_373, 1, x_372);
lean_ctor_set(x_373, 2, x_28);
x_374 = lean_array_uset(x_13, x_27, x_373);
x_375 = lean_unsigned_to_nat(4u);
x_376 = lean_nat_mul(x_371, x_375);
x_377 = lean_unsigned_to_nat(3u);
x_378 = lean_nat_div(x_376, x_377);
lean_dec(x_376);
x_379 = lean_array_get_size(x_374);
x_380 = lean_nat_dec_le(x_378, x_379);
lean_dec(x_379);
lean_dec(x_378);
if (x_380 == 0)
{
lean_object* x_381; lean_object* x_382; 
x_381 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_LeanLib_recCollectLocalModules_go___spec__3(x_374);
x_382 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_382, 0, x_371);
lean_ctor_set(x_382, 1, x_381);
x_241 = x_382;
goto block_369;
}
else
{
lean_object* x_383; 
x_383 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_383, 0, x_371);
lean_ctor_set(x_383, 1, x_374);
x_241 = x_383;
goto block_369;
}
block_369:
{
lean_object* x_242; lean_object* x_243; lean_object* x_277; lean_object* x_278; lean_object* x_290; lean_object* x_291; 
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_307; 
x_307 = lean_ctor_get(x_240, 0);
lean_inc(x_307);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_308 = lean_ctor_get(x_240, 1);
lean_inc(x_308);
lean_dec(x_240);
x_309 = lean_ctor_get(x_307, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_307, 1);
lean_inc(x_310);
lean_dec(x_307);
x_311 = lean_ctor_get(x_309, 0);
lean_inc(x_311);
lean_dec(x_309);
x_312 = lean_io_wait(x_311, x_308);
if (lean_obj_tag(x_312) == 0)
{
lean_object* x_313; 
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; 
x_314 = lean_ctor_get(x_313, 1);
lean_inc(x_314);
x_315 = lean_ctor_get(x_312, 1);
lean_inc(x_315);
lean_dec(x_312);
x_316 = lean_ctor_get(x_313, 0);
lean_inc(x_316);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 lean_ctor_release(x_313, 1);
 x_317 = x_313;
} else {
 lean_dec_ref(x_313);
 x_317 = lean_box(0);
}
x_318 = lean_ctor_get(x_314, 0);
lean_inc(x_318);
lean_dec(x_314);
x_319 = lean_array_get_size(x_318);
x_320 = lean_unsigned_to_nat(0u);
x_321 = lean_nat_dec_lt(x_320, x_319);
if (x_321 == 0)
{
lean_object* x_322; 
lean_dec(x_319);
lean_dec(x_318);
if (lean_is_scalar(x_317)) {
 x_322 = lean_alloc_ctor(0, 2, 0);
} else {
 x_322 = x_317;
}
lean_ctor_set(x_322, 0, x_316);
lean_ctor_set(x_322, 1, x_310);
x_290 = x_322;
x_291 = x_315;
goto block_306;
}
else
{
uint8_t x_323; 
x_323 = lean_nat_dec_le(x_319, x_319);
if (x_323 == 0)
{
lean_object* x_324; 
lean_dec(x_319);
lean_dec(x_318);
if (lean_is_scalar(x_317)) {
 x_324 = lean_alloc_ctor(0, 2, 0);
} else {
 x_324 = x_317;
}
lean_ctor_set(x_324, 0, x_316);
lean_ctor_set(x_324, 1, x_310);
x_290 = x_324;
x_291 = x_315;
goto block_306;
}
else
{
size_t x_325; size_t x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
lean_dec(x_317);
x_325 = 0;
x_326 = lean_usize_of_nat(x_319);
lean_dec(x_319);
x_327 = lean_box(0);
x_328 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_318, x_325, x_326, x_327, x_310, x_315);
lean_dec(x_318);
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_328, 1);
lean_inc(x_330);
lean_dec(x_328);
x_331 = lean_ctor_get(x_329, 1);
lean_inc(x_331);
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 lean_ctor_release(x_329, 1);
 x_332 = x_329;
} else {
 lean_dec_ref(x_329);
 x_332 = lean_box(0);
}
if (lean_is_scalar(x_332)) {
 x_333 = lean_alloc_ctor(0, 2, 0);
} else {
 x_333 = x_332;
}
lean_ctor_set(x_333, 0, x_316);
lean_ctor_set(x_333, 1, x_331);
x_290 = x_333;
x_291 = x_330;
goto block_306;
}
}
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; uint8_t x_341; 
x_334 = lean_ctor_get(x_313, 1);
lean_inc(x_334);
x_335 = lean_ctor_get(x_312, 1);
lean_inc(x_335);
lean_dec(x_312);
x_336 = lean_ctor_get(x_313, 0);
lean_inc(x_336);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 lean_ctor_release(x_313, 1);
 x_337 = x_313;
} else {
 lean_dec_ref(x_313);
 x_337 = lean_box(0);
}
x_338 = lean_ctor_get(x_334, 0);
lean_inc(x_338);
lean_dec(x_334);
x_339 = lean_array_get_size(x_338);
x_340 = lean_unsigned_to_nat(0u);
x_341 = lean_nat_dec_lt(x_340, x_339);
if (x_341 == 0)
{
lean_object* x_342; 
lean_dec(x_339);
lean_dec(x_338);
if (lean_is_scalar(x_337)) {
 x_342 = lean_alloc_ctor(1, 2, 0);
} else {
 x_342 = x_337;
}
lean_ctor_set(x_342, 0, x_336);
lean_ctor_set(x_342, 1, x_310);
x_290 = x_342;
x_291 = x_335;
goto block_306;
}
else
{
uint8_t x_343; 
x_343 = lean_nat_dec_le(x_339, x_339);
if (x_343 == 0)
{
lean_object* x_344; 
lean_dec(x_339);
lean_dec(x_338);
if (lean_is_scalar(x_337)) {
 x_344 = lean_alloc_ctor(1, 2, 0);
} else {
 x_344 = x_337;
}
lean_ctor_set(x_344, 0, x_336);
lean_ctor_set(x_344, 1, x_310);
x_290 = x_344;
x_291 = x_335;
goto block_306;
}
else
{
size_t x_345; size_t x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
lean_dec(x_337);
x_345 = 0;
x_346 = lean_usize_of_nat(x_339);
lean_dec(x_339);
x_347 = lean_box(0);
x_348 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_338, x_345, x_346, x_347, x_310, x_335);
lean_dec(x_338);
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_348, 1);
lean_inc(x_350);
lean_dec(x_348);
x_351 = lean_ctor_get(x_349, 1);
lean_inc(x_351);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 x_352 = x_349;
} else {
 lean_dec_ref(x_349);
 x_352 = lean_box(0);
}
if (lean_is_scalar(x_352)) {
 x_353 = lean_alloc_ctor(1, 2, 0);
} else {
 x_353 = x_352;
 lean_ctor_set_tag(x_353, 1);
}
lean_ctor_set(x_353, 0, x_336);
lean_ctor_set(x_353, 1, x_351);
x_290 = x_353;
x_291 = x_350;
goto block_306;
}
}
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
lean_dec(x_310);
lean_dec(x_241);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_354 = lean_ctor_get(x_312, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_312, 1);
lean_inc(x_355);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 x_356 = x_312;
} else {
 lean_dec_ref(x_312);
 x_356 = lean_box(0);
}
if (lean_is_scalar(x_356)) {
 x_357 = lean_alloc_ctor(1, 2, 0);
} else {
 x_357 = x_356;
}
lean_ctor_set(x_357, 0, x_354);
lean_ctor_set(x_357, 1, x_355);
return x_357;
}
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
lean_dec(x_241);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_358 = lean_ctor_get(x_240, 1);
lean_inc(x_358);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_359 = x_240;
} else {
 lean_dec_ref(x_240);
 x_359 = lean_box(0);
}
x_360 = lean_ctor_get(x_307, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_307, 1);
lean_inc(x_361);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 lean_ctor_release(x_307, 1);
 x_362 = x_307;
} else {
 lean_dec_ref(x_307);
 x_362 = lean_box(0);
}
if (lean_is_scalar(x_362)) {
 x_363 = lean_alloc_ctor(1, 2, 0);
} else {
 x_363 = x_362;
}
lean_ctor_set(x_363, 0, x_360);
lean_ctor_set(x_363, 1, x_361);
if (lean_is_scalar(x_359)) {
 x_364 = lean_alloc_ctor(0, 2, 0);
} else {
 x_364 = x_359;
}
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_364, 1, x_358);
return x_364;
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
lean_dec(x_241);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_365 = lean_ctor_get(x_240, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_240, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_367 = x_240;
} else {
 lean_dec_ref(x_240);
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
block_276:
{
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; size_t x_248; size_t x_249; lean_object* x_250; 
x_244 = lean_ctor_get(x_242, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_242, 1);
lean_inc(x_245);
lean_dec(x_242);
x_246 = lean_box(0);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_241);
lean_ctor_set(x_247, 1, x_3);
x_248 = lean_array_size(x_244);
x_249 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_250 = l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_recCollectLocalModules_go___spec__2(x_1, x_244, x_246, x_244, x_248, x_249, x_247, x_5, x_6, x_7, x_8, x_245, x_243);
lean_dec(x_244);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_250, 1);
lean_inc(x_253);
lean_dec(x_250);
x_254 = lean_ctor_get(x_251, 1);
lean_inc(x_254);
lean_dec(x_251);
x_255 = lean_ctor_get(x_252, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_252, 1);
lean_inc(x_256);
lean_dec(x_252);
x_257 = lean_array_push(x_256, x_2);
x_258 = lean_box(0);
x_259 = lean_apply_9(x_11, x_255, x_257, x_258, x_5, x_6, x_7, x_8, x_254, x_253);
return x_259;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_260 = lean_ctor_get(x_250, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_261 = x_250;
} else {
 lean_dec_ref(x_250);
 x_261 = lean_box(0);
}
x_262 = lean_ctor_get(x_251, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_251, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_264 = x_251;
} else {
 lean_dec_ref(x_251);
 x_264 = lean_box(0);
}
if (lean_is_scalar(x_264)) {
 x_265 = lean_alloc_ctor(1, 2, 0);
} else {
 x_265 = x_264;
}
lean_ctor_set(x_265, 0, x_262);
lean_ctor_set(x_265, 1, x_263);
if (lean_is_scalar(x_261)) {
 x_266 = lean_alloc_ctor(0, 2, 0);
} else {
 x_266 = x_261;
}
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_260);
return x_266;
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_267 = lean_ctor_get(x_250, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_250, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_269 = x_250;
} else {
 lean_dec_ref(x_250);
 x_269 = lean_box(0);
}
if (lean_is_scalar(x_269)) {
 x_270 = lean_alloc_ctor(1, 2, 0);
} else {
 x_270 = x_269;
}
lean_ctor_set(x_270, 0, x_267);
lean_ctor_set(x_270, 1, x_268);
return x_270;
}
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_241);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_271 = lean_ctor_get(x_242, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_242, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_273 = x_242;
} else {
 lean_dec_ref(x_242);
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
lean_ctor_set(x_275, 1, x_243);
return x_275;
}
}
block_289:
{
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_279 = lean_ctor_get(x_277, 0);
lean_inc(x_279);
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
x_282 = lean_ctor_get(x_280, 0);
lean_inc(x_282);
lean_dec(x_280);
if (lean_is_scalar(x_281)) {
 x_283 = lean_alloc_ctor(0, 2, 0);
} else {
 x_283 = x_281;
}
lean_ctor_set(x_283, 0, x_279);
lean_ctor_set(x_283, 1, x_282);
x_242 = x_283;
x_243 = x_278;
goto block_276;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_284 = lean_ctor_get(x_277, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_277, 1);
lean_inc(x_285);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 x_286 = x_277;
} else {
 lean_dec_ref(x_277);
 x_286 = lean_box(0);
}
x_287 = lean_ctor_get(x_285, 0);
lean_inc(x_287);
lean_dec(x_285);
if (lean_is_scalar(x_286)) {
 x_288 = lean_alloc_ctor(1, 2, 0);
} else {
 x_288 = x_286;
}
lean_ctor_set(x_288, 0, x_284);
lean_ctor_set(x_288, 1, x_287);
x_242 = x_288;
x_243 = x_278;
goto block_276;
}
}
block_306:
{
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_292 = lean_ctor_get(x_290, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_290, 1);
lean_inc(x_293);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 lean_ctor_release(x_290, 1);
 x_294 = x_290;
} else {
 lean_dec_ref(x_290);
 x_294 = lean_box(0);
}
x_295 = 0;
x_296 = l_Lake_BuildTrace_nil;
x_297 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_297, 0, x_293);
lean_ctor_set(x_297, 1, x_296);
lean_ctor_set_uint8(x_297, sizeof(void*)*2, x_295);
if (lean_is_scalar(x_294)) {
 x_298 = lean_alloc_ctor(0, 2, 0);
} else {
 x_298 = x_294;
}
lean_ctor_set(x_298, 0, x_292);
lean_ctor_set(x_298, 1, x_297);
x_277 = x_298;
x_278 = x_291;
goto block_289;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_299 = lean_ctor_get(x_290, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_290, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 lean_ctor_release(x_290, 1);
 x_301 = x_290;
} else {
 lean_dec_ref(x_290);
 x_301 = lean_box(0);
}
x_302 = 0;
x_303 = l_Lake_BuildTrace_nil;
x_304 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_304, 0, x_300);
lean_ctor_set(x_304, 1, x_303);
lean_ctor_set_uint8(x_304, sizeof(void*)*2, x_302);
if (lean_is_scalar(x_301)) {
 x_305 = lean_alloc_ctor(1, 2, 0);
} else {
 x_305 = x_301;
}
lean_ctor_set(x_305, 0, x_299);
lean_ctor_set(x_305, 1, x_304);
x_277 = x_305;
x_278 = x_291;
goto block_289;
}
}
}
}
}
else
{
lean_object* x_384; lean_object* x_385; 
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_2);
x_384 = lean_box(0);
x_385 = lean_apply_9(x_11, x_4, x_3, x_384, x_5, x_6, x_7, x_8, x_9, x_10);
return x_385;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lake_LeanLib_recCollectLocalModules_go___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Lake_LeanLib_recCollectLocalModules_go___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_recCollectLocalModules_go___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_recCollectLocalModules_go___spec__2(x_1, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_LeanLib_recCollectLocalModules_go___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_LeanLib_recCollectLocalModules_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_recCollectLocalModules___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_6, x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_uget(x_4, x_6);
x_18 = lean_ctor_get(x_7, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_dec(x_7);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_20 = l_Lake_LeanLib_recCollectLocalModules_go(x_1, x_17, x_19, x_18, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_ctor_set(x_22, 1, x_26);
lean_ctor_set(x_22, 0, x_27);
x_28 = 1;
x_29 = lean_usize_add(x_6, x_28);
x_6 = x_29;
x_7 = x_22;
x_12 = x_24;
x_13 = x_23;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; 
x_31 = lean_ctor_get(x_22, 0);
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_22);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = 1;
x_35 = lean_usize_add(x_6, x_34);
x_6 = x_35;
x_7 = x_33;
x_12 = x_24;
x_13 = x_23;
goto _start;
}
}
else
{
uint8_t x_37; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_37 = !lean_is_exclusive(x_20);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_20, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_21);
if (x_39 == 0)
{
return x_20;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_21, 0);
x_41 = lean_ctor_get(x_21, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_21);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_20, 0, x_42);
return x_20;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_20, 1);
lean_inc(x_43);
lean_dec(x_20);
x_44 = lean_ctor_get(x_21, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_21, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_46 = x_21;
} else {
 lean_dec_ref(x_21);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_43);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_49 = !lean_is_exclusive(x_20);
if (x_49 == 0)
{
return x_20;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_20, 0);
x_51 = lean_ctor_get(x_20, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_20);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_LeanLib_recCollectLocalModules___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_apply_6(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_apply_7(x_2, x_12, x_3, x_4, x_5, x_6, x_13, x_11);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_9, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_9, 0, x_20);
return x_9;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_dec(x_9);
x_22 = lean_ctor_get(x_10, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_24 = x_10;
} else {
 lean_dec_ref(x_10);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_9);
if (x_27 == 0)
{
return x_9;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_9, 0);
x_29 = lean_ctor_get(x_9, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_9);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_EquipT_bind___at_Lake_LeanLib_recCollectLocalModules___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_LeanLib_recCollectLocalModules___spec__2___rarg), 8, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_LeanLib_recCollectLocalModules___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_31; 
x_31 = lean_get_set_stdout(x_1, x_8);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = lean_ctor_get(x_35, 1);
x_40 = lean_get_set_stdout(x_32, x_36);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_35, 0, x_43);
x_9 = x_35;
x_10 = x_41;
goto block_30;
}
else
{
uint8_t x_44; 
lean_free_object(x_35);
lean_dec(x_39);
lean_dec(x_38);
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_40, 0);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_40);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_35, 0);
x_49 = lean_ctor_get(x_35, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_35);
x_50 = lean_get_set_stdout(x_32, x_36);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_49);
x_9 = x_54;
x_10 = x_51;
goto block_30;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_49);
lean_dec(x_48);
x_55 = lean_ctor_get(x_50, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_57 = x_50;
} else {
 lean_dec_ref(x_50);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_34, 1);
lean_inc(x_59);
lean_dec(x_34);
x_60 = !lean_is_exclusive(x_35);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_35, 0);
x_62 = lean_ctor_get(x_35, 1);
x_63 = lean_get_set_stdout(x_32, x_59);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_9 = x_35;
x_10 = x_64;
goto block_30;
}
else
{
uint8_t x_65; 
lean_free_object(x_35);
lean_dec(x_62);
lean_dec(x_61);
x_65 = !lean_is_exclusive(x_63);
if (x_65 == 0)
{
return x_63;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_63, 0);
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_63);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_35, 0);
x_70 = lean_ctor_get(x_35, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_35);
x_71 = lean_get_set_stdout(x_32, x_59);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_70);
x_9 = x_73;
x_10 = x_72;
goto block_30;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_70);
lean_dec(x_69);
x_74 = lean_ctor_get(x_71, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_76 = x_71;
} else {
 lean_dec_ref(x_71);
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
}
else
{
uint8_t x_78; 
lean_dec(x_32);
x_78 = !lean_is_exclusive(x_34);
if (x_78 == 0)
{
return x_34;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_34, 0);
x_80 = lean_ctor_get(x_34, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_34);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_82 = !lean_is_exclusive(x_31);
if (x_82 == 0)
{
return x_31;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_31, 0);
x_84 = lean_ctor_get(x_31, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_31);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
block_30:
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_14);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_19);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_LeanLib_recCollectLocalModules___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_31; 
x_31 = lean_get_set_stdin(x_1, x_8);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = lean_ctor_get(x_35, 1);
x_40 = lean_get_set_stdin(x_32, x_36);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_35, 0, x_43);
x_9 = x_35;
x_10 = x_41;
goto block_30;
}
else
{
uint8_t x_44; 
lean_free_object(x_35);
lean_dec(x_39);
lean_dec(x_38);
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_40, 0);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_40);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_35, 0);
x_49 = lean_ctor_get(x_35, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_35);
x_50 = lean_get_set_stdin(x_32, x_36);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_49);
x_9 = x_54;
x_10 = x_51;
goto block_30;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_49);
lean_dec(x_48);
x_55 = lean_ctor_get(x_50, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_57 = x_50;
} else {
 lean_dec_ref(x_50);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_34, 1);
lean_inc(x_59);
lean_dec(x_34);
x_60 = !lean_is_exclusive(x_35);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_35, 0);
x_62 = lean_ctor_get(x_35, 1);
x_63 = lean_get_set_stdin(x_32, x_59);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_9 = x_35;
x_10 = x_64;
goto block_30;
}
else
{
uint8_t x_65; 
lean_free_object(x_35);
lean_dec(x_62);
lean_dec(x_61);
x_65 = !lean_is_exclusive(x_63);
if (x_65 == 0)
{
return x_63;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_63, 0);
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_63);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_35, 0);
x_70 = lean_ctor_get(x_35, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_35);
x_71 = lean_get_set_stdin(x_32, x_59);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_70);
x_9 = x_73;
x_10 = x_72;
goto block_30;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_70);
lean_dec(x_69);
x_74 = lean_ctor_get(x_71, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_76 = x_71;
} else {
 lean_dec_ref(x_71);
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
}
else
{
uint8_t x_78; 
lean_dec(x_32);
x_78 = !lean_is_exclusive(x_34);
if (x_78 == 0)
{
return x_34;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_34, 0);
x_80 = lean_ctor_get(x_34, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_34);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_82 = !lean_is_exclusive(x_31);
if (x_82 == 0)
{
return x_31;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_31, 0);
x_84 = lean_ctor_get(x_31, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_31);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
block_30:
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_14);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_19);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_LeanLib_recCollectLocalModules___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_31; 
x_31 = lean_get_set_stderr(x_1, x_8);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = lean_ctor_get(x_35, 1);
x_40 = lean_get_set_stderr(x_32, x_36);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_35, 0, x_43);
x_9 = x_35;
x_10 = x_41;
goto block_30;
}
else
{
uint8_t x_44; 
lean_free_object(x_35);
lean_dec(x_39);
lean_dec(x_38);
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_40, 0);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_40);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_35, 0);
x_49 = lean_ctor_get(x_35, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_35);
x_50 = lean_get_set_stderr(x_32, x_36);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_49);
x_9 = x_54;
x_10 = x_51;
goto block_30;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_49);
lean_dec(x_48);
x_55 = lean_ctor_get(x_50, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_57 = x_50;
} else {
 lean_dec_ref(x_50);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_34, 1);
lean_inc(x_59);
lean_dec(x_34);
x_60 = !lean_is_exclusive(x_35);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_35, 0);
x_62 = lean_ctor_get(x_35, 1);
x_63 = lean_get_set_stderr(x_32, x_59);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_9 = x_35;
x_10 = x_64;
goto block_30;
}
else
{
uint8_t x_65; 
lean_free_object(x_35);
lean_dec(x_62);
lean_dec(x_61);
x_65 = !lean_is_exclusive(x_63);
if (x_65 == 0)
{
return x_63;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_63, 0);
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_63);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_35, 0);
x_70 = lean_ctor_get(x_35, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_35);
x_71 = lean_get_set_stderr(x_32, x_59);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_70);
x_9 = x_73;
x_10 = x_72;
goto block_30;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_70);
lean_dec(x_69);
x_74 = lean_ctor_get(x_71, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_76 = x_71;
} else {
 lean_dec_ref(x_71);
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
}
else
{
uint8_t x_78; 
lean_dec(x_32);
x_78 = !lean_is_exclusive(x_34);
if (x_78 == 0)
{
return x_34;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_34, 0);
x_80 = lean_ctor_get(x_34, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_34);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_82 = !lean_is_exclusive(x_31);
if (x_82 == 0)
{
return x_31;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_31, 0);
x_84 = lean_ctor_get(x_31, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_31);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
block_30:
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_14);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_19);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__1() {
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
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.String.Extra", 22, 22);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String.fromUTF8!", 16, 16);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid UTF-8 string", 20, 20);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__2;
x_2 = l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__3;
x_3 = lean_unsigned_to_nat(126u);
x_4 = lean_unsigned_to_nat(47u);
x_5 = l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__1;
x_10 = lean_st_mk_ref(x_9, x_8);
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
x_18 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_LeanLib_recCollectLocalModules___spec__5), 8, 2);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_1);
x_19 = l_IO_withStdin___at_Lake_LeanLib_recCollectLocalModules___spec__6(x_16, x_18, x_3, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_20, 1);
x_25 = lean_st_ref_get(x_14, x_21);
lean_dec(x_14);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_string_validate_utf8(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_28);
x_30 = l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__5;
x_31 = l_panic___at_String_fromUTF8_x21___spec__1(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_23);
lean_ctor_set(x_20, 0, x_32);
lean_ctor_set(x_25, 0, x_20);
return x_25;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_string_from_utf8_unchecked(x_28);
lean_dec(x_28);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_23);
lean_ctor_set(x_20, 0, x_34);
lean_ctor_set(x_25, 0, x_20);
return x_25;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_ctor_get(x_25, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_25);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_string_validate_utf8(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_37);
x_39 = l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__5;
x_40 = l_panic___at_String_fromUTF8_x21___spec__1(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_23);
lean_ctor_set(x_20, 0, x_41);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_20);
lean_ctor_set(x_42, 1, x_36);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_string_from_utf8_unchecked(x_37);
lean_dec(x_37);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_23);
lean_ctor_set(x_20, 0, x_44);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_20);
lean_ctor_set(x_45, 1, x_36);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_free_object(x_20);
lean_dec(x_24);
lean_dec(x_23);
x_46 = !lean_is_exclusive(x_25);
if (x_46 == 0)
{
return x_25;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_25, 0);
x_48 = lean_ctor_get(x_25, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_25);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_20, 0);
x_51 = lean_ctor_get(x_20, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_20);
x_52 = lean_st_ref_get(x_14, x_21);
lean_dec(x_14);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
x_56 = lean_ctor_get(x_53, 0);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_string_validate_utf8(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_56);
x_58 = l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__5;
x_59 = l_panic___at_String_fromUTF8_x21___spec__1(x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_50);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_51);
if (lean_is_scalar(x_55)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_55;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_54);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_string_from_utf8_unchecked(x_56);
lean_dec(x_56);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_50);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_51);
if (lean_is_scalar(x_55)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_55;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_54);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_51);
lean_dec(x_50);
x_67 = lean_ctor_get(x_52, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_52, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_69 = x_52;
} else {
 lean_dec_ref(x_52);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_14);
x_71 = !lean_is_exclusive(x_19);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_19, 0);
lean_dec(x_72);
x_73 = !lean_is_exclusive(x_20);
if (x_73 == 0)
{
return x_19;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_20, 0);
x_75 = lean_ctor_get(x_20, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_20);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set(x_19, 0, x_76);
return x_19;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_19, 1);
lean_inc(x_77);
lean_dec(x_19);
x_78 = lean_ctor_get(x_20, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_20, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_80 = x_20;
} else {
 lean_dec_ref(x_20);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_77);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_14);
x_83 = !lean_is_exclusive(x_19);
if (x_83 == 0)
{
return x_19;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_19, 0);
x_85 = lean_ctor_get(x_19, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_19);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_inc(x_17);
x_87 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lake_LeanLib_recCollectLocalModules___spec__7), 8, 2);
lean_closure_set(x_87, 0, x_17);
lean_closure_set(x_87, 1, x_1);
x_88 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_LeanLib_recCollectLocalModules___spec__5), 8, 2);
lean_closure_set(x_88, 0, x_17);
lean_closure_set(x_88, 1, x_87);
x_89 = l_IO_withStdin___at_Lake_LeanLib_recCollectLocalModules___spec__6(x_16, x_88, x_3, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = !lean_is_exclusive(x_90);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_90, 0);
x_94 = lean_ctor_get(x_90, 1);
x_95 = lean_st_ref_get(x_14, x_91);
lean_dec(x_14);
if (lean_obj_tag(x_95) == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_97 = lean_ctor_get(x_95, 0);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec(x_97);
x_99 = lean_string_validate_utf8(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_98);
x_100 = l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__5;
x_101 = l_panic___at_String_fromUTF8_x21___spec__1(x_100);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_93);
lean_ctor_set(x_90, 0, x_102);
lean_ctor_set(x_95, 0, x_90);
return x_95;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_string_from_utf8_unchecked(x_98);
lean_dec(x_98);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_93);
lean_ctor_set(x_90, 0, x_104);
lean_ctor_set(x_95, 0, x_90);
return x_95;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_105 = lean_ctor_get(x_95, 0);
x_106 = lean_ctor_get(x_95, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_95);
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_string_validate_utf8(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_107);
x_109 = l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__5;
x_110 = l_panic___at_String_fromUTF8_x21___spec__1(x_109);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_93);
lean_ctor_set(x_90, 0, x_111);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_90);
lean_ctor_set(x_112, 1, x_106);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_string_from_utf8_unchecked(x_107);
lean_dec(x_107);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_93);
lean_ctor_set(x_90, 0, x_114);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_90);
lean_ctor_set(x_115, 1, x_106);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_free_object(x_90);
lean_dec(x_94);
lean_dec(x_93);
x_116 = !lean_is_exclusive(x_95);
if (x_116 == 0)
{
return x_95;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_95, 0);
x_118 = lean_ctor_get(x_95, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_95);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_90, 0);
x_121 = lean_ctor_get(x_90, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_90);
x_122 = lean_st_ref_get(x_14, x_91);
lean_dec(x_14);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
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
x_126 = lean_ctor_get(x_123, 0);
lean_inc(x_126);
lean_dec(x_123);
x_127 = lean_string_validate_utf8(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_126);
x_128 = l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__5;
x_129 = l_panic___at_String_fromUTF8_x21___spec__1(x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_120);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_121);
if (lean_is_scalar(x_125)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_125;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_124);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_133 = lean_string_from_utf8_unchecked(x_126);
lean_dec(x_126);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_120);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_121);
if (lean_is_scalar(x_125)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_125;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_124);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_121);
lean_dec(x_120);
x_137 = lean_ctor_get(x_122, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_122, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_139 = x_122;
} else {
 lean_dec_ref(x_122);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
}
else
{
uint8_t x_141; 
lean_dec(x_14);
x_141 = !lean_is_exclusive(x_89);
if (x_141 == 0)
{
lean_object* x_142; uint8_t x_143; 
x_142 = lean_ctor_get(x_89, 0);
lean_dec(x_142);
x_143 = !lean_is_exclusive(x_90);
if (x_143 == 0)
{
return x_89;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_90, 0);
x_145 = lean_ctor_get(x_90, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_90);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
lean_ctor_set(x_89, 0, x_146);
return x_89;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_147 = lean_ctor_get(x_89, 1);
lean_inc(x_147);
lean_dec(x_89);
x_148 = lean_ctor_get(x_90, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_90, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_150 = x_90;
} else {
 lean_dec_ref(x_90);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_149);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_147);
return x_152;
}
}
}
else
{
uint8_t x_153; 
lean_dec(x_14);
x_153 = !lean_is_exclusive(x_89);
if (x_153 == 0)
{
return x_89;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_89, 0);
x_155 = lean_ctor_get(x_89, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_89);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_157 = !lean_is_exclusive(x_13);
if (x_157 == 0)
{
return x_13;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_13, 0);
x_159 = lean_ctor_get(x_13, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_13);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
else
{
uint8_t x_161; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_161 = !lean_is_exclusive(x_10);
if (x_161 == 0)
{
return x_10;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_10, 0);
x_163 = lean_ctor_get(x_10, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_10);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
static lean_object* _init_l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stdout/stderr:\n", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_91; lean_object* x_92; 
x_8 = lean_array_get_size(x_6);
x_91 = 1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_92 = l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4(x_1, x_91, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec(x_93);
x_97 = lean_ctor_get(x_94, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_94, 1);
lean_inc(x_98);
lean_dec(x_94);
x_99 = lean_string_utf8_byte_size(x_97);
x_100 = lean_unsigned_to_nat(0u);
x_101 = lean_nat_dec_eq(x_99, x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_102 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_97, x_99, x_100);
x_103 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_97, x_102, x_99);
x_104 = lean_string_utf8_extract(x_97, x_102, x_103);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_97);
x_105 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__2;
x_106 = lean_string_append(x_105, x_104);
lean_dec(x_104);
x_107 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__1;
x_108 = lean_string_append(x_106, x_107);
x_109 = 1;
x_110 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set_uint8(x_110, sizeof(void*)*1, x_109);
x_111 = lean_array_push(x_96, x_110);
x_112 = lean_box(0);
x_113 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___lambda__1(x_98, x_112, x_2, x_3, x_4, x_5, x_111, x_95);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_9 = x_114;
x_10 = x_115;
goto block_90;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_99);
lean_dec(x_97);
x_116 = lean_box(0);
x_117 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___lambda__1(x_98, x_116, x_2, x_3, x_4, x_5, x_96, x_95);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_9 = x_118;
x_10 = x_119;
goto block_90;
}
}
else
{
lean_object* x_120; uint8_t x_121; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_120 = lean_ctor_get(x_92, 1);
lean_inc(x_120);
lean_dec(x_92);
x_121 = !lean_is_exclusive(x_93);
if (x_121 == 0)
{
x_9 = x_93;
x_10 = x_120;
goto block_90;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_93, 0);
x_123 = lean_ctor_get(x_93, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_93);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_9 = x_124;
x_10 = x_120;
goto block_90;
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_125 = !lean_is_exclusive(x_92);
if (x_125 == 0)
{
return x_92;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_92, 0);
x_127 = lean_ctor_get(x_92, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_92);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
block_90:
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 1);
x_14 = lean_array_get_size(x_13);
x_15 = lean_nat_dec_lt(x_8, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec(x_8);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_inc(x_13);
x_17 = l_Array_shrink___rarg(x_13, x_8);
x_18 = l_Array_extract___rarg(x_13, x_8, x_14);
lean_dec(x_14);
lean_dec(x_13);
x_19 = lean_alloc_closure((void*)(l_Lake_JobResult_prependLog___rarg), 2, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_dec(x_22);
x_23 = l_Task_Priority_default;
x_24 = 1;
x_25 = lean_task_map(x_19, x_21, x_23, x_24);
x_26 = lean_box(0);
lean_ctor_set(x_12, 1, x_26);
lean_ctor_set(x_12, 0, x_25);
lean_ctor_set(x_9, 1, x_17);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_9);
lean_ctor_set(x_27, 1, x_10);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_12, 0);
x_29 = lean_ctor_get(x_12, 2);
x_30 = lean_ctor_get_uint8(x_12, sizeof(void*)*3);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_12);
x_31 = l_Task_Priority_default;
x_32 = 1;
x_33 = lean_task_map(x_19, x_28, x_31, x_32);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_29);
lean_ctor_set_uint8(x_35, sizeof(void*)*3, x_30);
lean_ctor_set(x_9, 1, x_17);
lean_ctor_set(x_9, 0, x_35);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_9);
lean_ctor_set(x_36, 1, x_10);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_9, 0);
x_38 = lean_ctor_get(x_9, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_9);
x_39 = lean_array_get_size(x_38);
x_40 = lean_nat_dec_lt(x_8, x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_39);
lean_dec(x_8);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_10);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_inc(x_38);
x_43 = l_Array_shrink___rarg(x_38, x_8);
x_44 = l_Array_extract___rarg(x_38, x_8, x_39);
lean_dec(x_39);
lean_dec(x_38);
x_45 = lean_alloc_closure((void*)(l_Lake_JobResult_prependLog___rarg), 2, 1);
lean_closure_set(x_45, 0, x_44);
x_46 = lean_ctor_get(x_37, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_37, 2);
lean_inc(x_47);
x_48 = lean_ctor_get_uint8(x_37, sizeof(void*)*3);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 x_49 = x_37;
} else {
 lean_dec_ref(x_37);
 x_49 = lean_box(0);
}
x_50 = l_Task_Priority_default;
x_51 = 1;
x_52 = lean_task_map(x_45, x_46, x_50, x_51);
x_53 = lean_box(0);
if (lean_is_scalar(x_49)) {
 x_54 = lean_alloc_ctor(0, 3, 1);
} else {
 x_54 = x_49;
}
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_47);
lean_ctor_set_uint8(x_54, sizeof(void*)*3, x_48);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_43);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_10);
return x_56;
}
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_9);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_58 = lean_ctor_get(x_9, 1);
x_59 = lean_ctor_get(x_9, 0);
lean_dec(x_59);
lean_inc(x_58);
x_60 = l_Array_shrink___rarg(x_58, x_8);
x_61 = lean_array_get_size(x_58);
x_62 = l_Array_extract___rarg(x_58, x_8, x_61);
lean_dec(x_61);
lean_dec(x_58);
x_63 = 0;
x_64 = l_Lake_BuildTrace_nil;
x_65 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*2, x_63);
x_66 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_9, 1, x_65);
lean_ctor_set(x_9, 0, x_66);
x_67 = lean_task_pure(x_9);
x_68 = lean_box(0);
x_69 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__1;
x_70 = 0;
x_71 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_68);
lean_ctor_set(x_71, 2, x_69);
lean_ctor_set_uint8(x_71, sizeof(void*)*3, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_60);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_10);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_74 = lean_ctor_get(x_9, 1);
lean_inc(x_74);
lean_dec(x_9);
lean_inc(x_74);
x_75 = l_Array_shrink___rarg(x_74, x_8);
x_76 = lean_array_get_size(x_74);
x_77 = l_Array_extract___rarg(x_74, x_8, x_76);
lean_dec(x_76);
lean_dec(x_74);
x_78 = 0;
x_79 = l_Lake_BuildTrace_nil;
x_80 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set_uint8(x_80, sizeof(void*)*2, x_78);
x_81 = lean_unsigned_to_nat(0u);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
x_83 = lean_task_pure(x_82);
x_84 = lean_box(0);
x_85 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__1;
x_86 = 0;
x_87 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_87, 0, x_83);
lean_ctor_set(x_87, 1, x_84);
lean_ctor_set(x_87, 2, x_85);
lean_ctor_set_uint8(x_87, sizeof(void*)*3, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_75);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_10);
return x_89;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_LeanLib_getModuleArray(x_1, x_7);
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
lean_ctor_set(x_11, 1, x_6);
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
lean_ctor_set(x_14, 1, x_6);
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
x_21 = lean_array_get_size(x_6);
x_22 = lean_array_push(x_6, x_20);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
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
x_29 = lean_array_get_size(x_6);
x_30 = lean_array_push(x_6, x_28);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_25);
return x_32;
}
}
}
}
static lean_object* _init_l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_10 = lean_box(0);
x_11 = l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__3;
lean_inc(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_1);
x_13 = lean_array_size(x_3);
x_14 = 0;
x_15 = l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_recCollectLocalModules___spec__1(x_2, x_3, x_10, x_3, x_13, x_14, x_12, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_16, 1);
x_22 = lean_ctor_get(x_16, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_17, 1);
x_25 = lean_ctor_get(x_17, 0);
lean_dec(x_25);
x_26 = 0;
x_27 = l_Lake_BuildTrace_nil;
x_28 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*2, x_26);
lean_ctor_set(x_16, 1, x_28);
lean_ctor_set(x_16, 0, x_24);
x_29 = lean_task_pure(x_16);
x_30 = lean_box(0);
x_31 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__1;
x_32 = 0;
x_33 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_30);
lean_ctor_set(x_33, 2, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*3, x_32);
lean_ctor_set(x_17, 1, x_21);
lean_ctor_set(x_17, 0, x_33);
lean_ctor_set(x_15, 0, x_17);
return x_15;
}
else
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_34 = lean_ctor_get(x_17, 1);
lean_inc(x_34);
lean_dec(x_17);
x_35 = 0;
x_36 = l_Lake_BuildTrace_nil;
x_37 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*2, x_35);
lean_ctor_set(x_16, 1, x_37);
lean_ctor_set(x_16, 0, x_34);
x_38 = lean_task_pure(x_16);
x_39 = lean_box(0);
x_40 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__1;
x_41 = 0;
x_42 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_39);
lean_ctor_set(x_42, 2, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*3, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_21);
lean_ctor_set(x_15, 0, x_43);
return x_15;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; 
x_44 = lean_ctor_get(x_16, 1);
lean_inc(x_44);
lean_dec(x_16);
x_45 = lean_ctor_get(x_17, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_46 = x_17;
} else {
 lean_dec_ref(x_17);
 x_46 = lean_box(0);
}
x_47 = 0;
x_48 = l_Lake_BuildTrace_nil;
x_49 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*2, x_47);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_task_pure(x_50);
x_52 = lean_box(0);
x_53 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__1;
x_54 = 0;
x_55 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_52);
lean_ctor_set(x_55, 2, x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*3, x_54);
if (lean_is_scalar(x_46)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_46;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_44);
lean_ctor_set(x_15, 0, x_56);
return x_15;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_57 = lean_ctor_get(x_15, 1);
lean_inc(x_57);
lean_dec(x_15);
x_58 = lean_ctor_get(x_16, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_59 = x_16;
} else {
 lean_dec_ref(x_16);
 x_59 = lean_box(0);
}
x_60 = lean_ctor_get(x_17, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_61 = x_17;
} else {
 lean_dec_ref(x_17);
 x_61 = lean_box(0);
}
x_62 = 0;
x_63 = l_Lake_BuildTrace_nil;
x_64 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_64, 0, x_1);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*2, x_62);
if (lean_is_scalar(x_59)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_59;
}
lean_ctor_set(x_65, 0, x_60);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_task_pure(x_65);
x_67 = lean_box(0);
x_68 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__1;
x_69 = 0;
x_70 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_70, 0, x_66);
lean_ctor_set(x_70, 1, x_67);
lean_ctor_set(x_70, 2, x_68);
lean_ctor_set_uint8(x_70, sizeof(void*)*3, x_69);
if (lean_is_scalar(x_61)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_61;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_58);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_57);
return x_72;
}
}
else
{
uint8_t x_73; 
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_15);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_15, 0);
lean_dec(x_74);
x_75 = !lean_is_exclusive(x_16);
if (x_75 == 0)
{
return x_15;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_16, 0);
x_77 = lean_ctor_get(x_16, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_16);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
lean_ctor_set(x_15, 0, x_78);
return x_15;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_79 = lean_ctor_get(x_15, 1);
lean_inc(x_79);
lean_dec(x_15);
x_80 = lean_ctor_get(x_16, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_16, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_82 = x_16;
} else {
 lean_dec_ref(x_16);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_79);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_15);
if (x_85 == 0)
{
return x_15;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_15, 0);
x_87 = lean_ctor_get(x_15, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_15);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
static lean_object* _init_l_Lake_LeanLib_recCollectLocalModules___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lake_LeanLib_recCollectLocalModules___lambda__1___boxed), 7, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
x_10 = lean_alloc_closure((void*)(l_Lake_LeanLib_recCollectLocalModules___lambda__2___boxed), 9, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_1);
x_11 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_LeanLib_recCollectLocalModules___spec__2___rarg), 8, 2);
lean_closure_set(x_11, 0, x_8);
lean_closure_set(x_11, 1, x_10);
x_12 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3(x_11, x_2, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_recCollectLocalModules___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lake_LeanLib_recCollectLocalModules___spec__1(x_1, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_LeanLib_recCollectLocalModules___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_LeanLib_recCollectLocalModules___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___spec__2___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___spec__2___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__1;
x_8 = lean_string_append(x_7, x_4);
lean_dec(x_4);
x_9 = lean_string_append(x_8, x_7);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = 1;
x_12 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___spec__2___closed__1;
x_13 = l_Lean_Name_toString(x_10, x_11, x_12);
x_14 = lean_string_append(x_9, x_13);
lean_dec(x_13);
x_15 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___spec__2___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_2 = x_18;
x_4 = x_16;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLib_modulesFacetConfig___spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = 1;
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___spec__2___closed__1;
x_11 = l_Lean_Name_toString(x_8, x_9, x_10);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_15 = lean_array_uset(x_7, x_2, x_12);
x_2 = x_14;
x_3 = x_15;
goto _start;
}
}
}
static lean_object* _init_l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_sub(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__2;
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__3;
x_4 = l_Substring_prevn(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__4;
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__5;
x_4 = lean_string_utf8_extract(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__6;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_3, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__6;
return x_8;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__1;
x_12 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___spec__2(x_2, x_9, x_10, x_11);
lean_dec(x_2);
x_13 = lean_string_utf8_byte_size(x_12);
lean_inc(x_13);
lean_inc(x_12);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_nat_sub(x_13, x_4);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Substring_prevn(x_14, x_16, x_15);
lean_dec(x_14);
x_18 = lean_nat_add(x_4, x_17);
lean_dec(x_17);
x_19 = lean_string_utf8_extract(x_12, x_4, x_18);
lean_dec(x_18);
lean_dec(x_12);
return x_19;
}
}
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_array_size(x_2);
x_21 = 0;
x_22 = l_Array_mapMUnsafe_map___at_Lake_LeanLib_modulesFacetConfig___spec__3(x_20, x_21, x_2);
x_23 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Lean_Json_compress(x_23);
return x_24;
}
}
}
static lean_object* _init_l_Lake_LeanLib_modulesFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_lib", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_modulesFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanLib_modulesFacetConfig___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLib_modulesFacetConfig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_recCollectLocalModules), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_modulesFacetConfig___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_modulesFacetConfig___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lake_LeanLib_modulesFacetConfig___closed__2;
x_2 = l_Lake_LeanLib_modulesFacetConfig___closed__3;
x_3 = lean_box(0);
x_4 = 0;
x_5 = l_Lake_LeanLib_modulesFacetConfig___closed__4;
x_6 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_4);
return x_6;
}
}
static lean_object* _init_l_Lake_LeanLib_modulesFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_LeanLib_modulesFacetConfig___closed__5;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___spec__2___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___spec__2___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLib_modulesFacetConfig___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_LeanLib_modulesFacetConfig___spec__3(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildLean___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_array_uget(x_1, x_2);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lake_Module_keyword;
x_16 = l_Lake_Module_leanArtsFacet;
x_17 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_12);
lean_ctor_set(x_17, 3, x_16);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = lean_apply_6(x_5, x_17, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = l_Lake_Job_mix___rarg(x_4, x_21);
x_24 = 1;
x_25 = lean_usize_add(x_2, x_24);
x_2 = x_25;
x_4 = x_23;
x_9 = x_22;
x_10 = x_20;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_18, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_19);
if (x_29 == 0)
{
return x_18;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_19, 0);
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_19);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_18, 0, x_32);
return x_18;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_dec(x_18);
x_34 = lean_ctor_get(x_19, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_36 = x_19;
} else {
 lean_dec_ref(x_19);
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
else
{
uint8_t x_39; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_39 = !lean_is_exclusive(x_18);
if (x_39 == 0)
{
return x_18;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_18, 0);
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_18);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_4);
lean_ctor_set(x_43, 1, x_9);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_10);
return x_44;
}
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildLean___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
x_2 = 0;
x_3 = l_Lake_BuildTrace_nil;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildLean___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanLib_recBuildLean___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildLean___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_LeanLib_recBuildLean___closed__2;
x_2 = lean_task_pure(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildLean___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lake_LeanLib_recBuildLean___closed__3;
x_2 = l_Lake_instDataKindUnit;
x_3 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__1;
x_4 = 0;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildLean(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_48; lean_object* x_49; lean_object* x_65; lean_object* x_66; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_90 = lean_ctor_get(x_1, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_1, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = l_Lake_LeanLib_modulesFacetConfig___closed__2;
x_95 = l_Lake_LeanLib_modulesFacet;
x_96 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
lean_ctor_set(x_96, 2, x_1);
lean_ctor_set(x_96, 3, x_95);
lean_inc(x_2);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_97 = lean_apply_6(x_2, x_96, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_ctor_get(x_100, 0);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_io_wait(x_102, x_99);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_107 = !lean_is_exclusive(x_104);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_108 = lean_ctor_get(x_104, 0);
x_109 = lean_ctor_get(x_104, 1);
lean_dec(x_109);
x_110 = lean_ctor_get(x_105, 0);
lean_inc(x_110);
lean_dec(x_105);
x_111 = lean_array_get_size(x_110);
x_112 = lean_unsigned_to_nat(0u);
x_113 = lean_nat_dec_lt(x_112, x_111);
if (x_113 == 0)
{
lean_dec(x_111);
lean_dec(x_110);
lean_ctor_set(x_104, 1, x_101);
x_65 = x_104;
x_66 = x_106;
goto block_89;
}
else
{
uint8_t x_114; 
x_114 = lean_nat_dec_le(x_111, x_111);
if (x_114 == 0)
{
lean_dec(x_111);
lean_dec(x_110);
lean_ctor_set(x_104, 1, x_101);
x_65 = x_104;
x_66 = x_106;
goto block_89;
}
else
{
size_t x_115; size_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
lean_free_object(x_104);
x_115 = 0;
x_116 = lean_usize_of_nat(x_111);
lean_dec(x_111);
x_117 = lean_box(0);
x_118 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_110, x_115, x_116, x_117, x_101, x_106);
lean_dec(x_110);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = !lean_is_exclusive(x_119);
if (x_121 == 0)
{
lean_object* x_122; 
x_122 = lean_ctor_get(x_119, 0);
lean_dec(x_122);
lean_ctor_set(x_119, 0, x_108);
x_65 = x_119;
x_66 = x_120;
goto block_89;
}
else
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_119, 1);
lean_inc(x_123);
lean_dec(x_119);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_108);
lean_ctor_set(x_124, 1, x_123);
x_65 = x_124;
x_66 = x_120;
goto block_89;
}
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_125 = lean_ctor_get(x_104, 0);
lean_inc(x_125);
lean_dec(x_104);
x_126 = lean_ctor_get(x_105, 0);
lean_inc(x_126);
lean_dec(x_105);
x_127 = lean_array_get_size(x_126);
x_128 = lean_unsigned_to_nat(0u);
x_129 = lean_nat_dec_lt(x_128, x_127);
if (x_129 == 0)
{
lean_object* x_130; 
lean_dec(x_127);
lean_dec(x_126);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_125);
lean_ctor_set(x_130, 1, x_101);
x_65 = x_130;
x_66 = x_106;
goto block_89;
}
else
{
uint8_t x_131; 
x_131 = lean_nat_dec_le(x_127, x_127);
if (x_131 == 0)
{
lean_object* x_132; 
lean_dec(x_127);
lean_dec(x_126);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_125);
lean_ctor_set(x_132, 1, x_101);
x_65 = x_132;
x_66 = x_106;
goto block_89;
}
else
{
size_t x_133; size_t x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_133 = 0;
x_134 = lean_usize_of_nat(x_127);
lean_dec(x_127);
x_135 = lean_box(0);
x_136 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_126, x_133, x_134, x_135, x_101, x_106);
lean_dec(x_126);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
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
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_125);
lean_ctor_set(x_141, 1, x_139);
x_65 = x_141;
x_66 = x_138;
goto block_89;
}
}
}
}
else
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_142 = lean_ctor_get(x_104, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_103, 1);
lean_inc(x_143);
lean_dec(x_103);
x_144 = !lean_is_exclusive(x_104);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_145 = lean_ctor_get(x_104, 0);
x_146 = lean_ctor_get(x_104, 1);
lean_dec(x_146);
x_147 = lean_ctor_get(x_142, 0);
lean_inc(x_147);
lean_dec(x_142);
x_148 = lean_array_get_size(x_147);
x_149 = lean_unsigned_to_nat(0u);
x_150 = lean_nat_dec_lt(x_149, x_148);
if (x_150 == 0)
{
lean_dec(x_148);
lean_dec(x_147);
lean_ctor_set(x_104, 1, x_101);
x_65 = x_104;
x_66 = x_143;
goto block_89;
}
else
{
uint8_t x_151; 
x_151 = lean_nat_dec_le(x_148, x_148);
if (x_151 == 0)
{
lean_dec(x_148);
lean_dec(x_147);
lean_ctor_set(x_104, 1, x_101);
x_65 = x_104;
x_66 = x_143;
goto block_89;
}
else
{
size_t x_152; size_t x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
lean_free_object(x_104);
x_152 = 0;
x_153 = lean_usize_of_nat(x_148);
lean_dec(x_148);
x_154 = lean_box(0);
x_155 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_147, x_152, x_153, x_154, x_101, x_143);
lean_dec(x_147);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_158 = !lean_is_exclusive(x_156);
if (x_158 == 0)
{
lean_object* x_159; 
x_159 = lean_ctor_get(x_156, 0);
lean_dec(x_159);
lean_ctor_set_tag(x_156, 1);
lean_ctor_set(x_156, 0, x_145);
x_65 = x_156;
x_66 = x_157;
goto block_89;
}
else
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_156, 1);
lean_inc(x_160);
lean_dec(x_156);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_145);
lean_ctor_set(x_161, 1, x_160);
x_65 = x_161;
x_66 = x_157;
goto block_89;
}
}
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_162 = lean_ctor_get(x_104, 0);
lean_inc(x_162);
lean_dec(x_104);
x_163 = lean_ctor_get(x_142, 0);
lean_inc(x_163);
lean_dec(x_142);
x_164 = lean_array_get_size(x_163);
x_165 = lean_unsigned_to_nat(0u);
x_166 = lean_nat_dec_lt(x_165, x_164);
if (x_166 == 0)
{
lean_object* x_167; 
lean_dec(x_164);
lean_dec(x_163);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_162);
lean_ctor_set(x_167, 1, x_101);
x_65 = x_167;
x_66 = x_143;
goto block_89;
}
else
{
uint8_t x_168; 
x_168 = lean_nat_dec_le(x_164, x_164);
if (x_168 == 0)
{
lean_object* x_169; 
lean_dec(x_164);
lean_dec(x_163);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_162);
lean_ctor_set(x_169, 1, x_101);
x_65 = x_169;
x_66 = x_143;
goto block_89;
}
else
{
size_t x_170; size_t x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_170 = 0;
x_171 = lean_usize_of_nat(x_164);
lean_dec(x_164);
x_172 = lean_box(0);
x_173 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_163, x_170, x_171, x_172, x_101, x_143);
lean_dec(x_163);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
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
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 2, 0);
} else {
 x_178 = x_177;
 lean_ctor_set_tag(x_178, 1);
}
lean_ctor_set(x_178, 0, x_162);
lean_ctor_set(x_178, 1, x_176);
x_65 = x_178;
x_66 = x_175;
goto block_89;
}
}
}
}
}
else
{
uint8_t x_179; 
lean_dec(x_101);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_179 = !lean_is_exclusive(x_103);
if (x_179 == 0)
{
return x_103;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_103, 0);
x_181 = lean_ctor_get(x_103, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_103);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
}
}
else
{
uint8_t x_183; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_183 = !lean_is_exclusive(x_97);
if (x_183 == 0)
{
lean_object* x_184; uint8_t x_185; 
x_184 = lean_ctor_get(x_97, 0);
lean_dec(x_184);
x_185 = !lean_is_exclusive(x_98);
if (x_185 == 0)
{
return x_97;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_98, 0);
x_187 = lean_ctor_get(x_98, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_98);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
lean_ctor_set(x_97, 0, x_188);
return x_97;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_189 = lean_ctor_get(x_97, 1);
lean_inc(x_189);
lean_dec(x_97);
x_190 = lean_ctor_get(x_98, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_98, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_192 = x_98;
} else {
 lean_dec_ref(x_98);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(1, 2, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_190);
lean_ctor_set(x_193, 1, x_191);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_189);
return x_194;
}
}
}
else
{
uint8_t x_195; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_195 = !lean_is_exclusive(x_97);
if (x_195 == 0)
{
return x_97;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_97, 0);
x_197 = lean_ctor_get(x_97, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_97);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
block_47:
{
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 1);
x_13 = lean_array_get_size(x_11);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = l_Lake_LeanLib_recBuildLean___closed__4;
lean_ctor_set(x_8, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_13, x_13);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = l_Lake_LeanLib_recBuildLean___closed__4;
lean_ctor_set(x_8, 0, x_19);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_9);
return x_20;
}
else
{
size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_8);
x_21 = 0;
x_22 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_23 = l_Lake_LeanLib_recBuildLean___closed__4;
x_24 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildLean___spec__1(x_11, x_21, x_22, x_23, x_2, x_3, x_4, x_5, x_12, x_9);
lean_dec(x_11);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_8);
x_27 = lean_array_get_size(x_25);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_dec_lt(x_28, x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = l_Lake_LeanLib_recBuildLean___closed__4;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_9);
return x_32;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_27, x_27);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = l_Lake_LeanLib_recBuildLean___closed__4;
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_26);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_9);
return x_36;
}
else
{
size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; 
x_37 = 0;
x_38 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_39 = l_Lake_LeanLib_recBuildLean___closed__4;
x_40 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildLean___spec__1(x_25, x_37, x_38, x_39, x_2, x_3, x_4, x_5, x_26, x_9);
lean_dec(x_25);
return x_40;
}
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_8);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_8);
lean_ctor_set(x_42, 1, x_9);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_8, 0);
x_44 = lean_ctor_get(x_8, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_8);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_9);
return x_46;
}
}
}
block_64:
{
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_48, 1);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec(x_51);
lean_ctor_set(x_48, 1, x_52);
x_8 = x_48;
x_9 = x_49;
goto block_47;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_48, 0);
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_48);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_55);
x_8 = x_56;
x_9 = x_49;
goto block_47;
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_48);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_48, 1);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec(x_58);
lean_ctor_set(x_48, 1, x_59);
x_8 = x_48;
x_9 = x_49;
goto block_47;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_48, 0);
x_61 = lean_ctor_get(x_48, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_48);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
x_8 = x_63;
x_9 = x_49;
goto block_47;
}
}
}
block_89:
{
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_65);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_65, 1);
x_69 = 0;
x_70 = l_Lake_BuildTrace_nil;
x_71 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set_uint8(x_71, sizeof(void*)*2, x_69);
lean_ctor_set(x_65, 1, x_71);
x_48 = x_65;
x_49 = x_66;
goto block_64;
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_72 = lean_ctor_get(x_65, 0);
x_73 = lean_ctor_get(x_65, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_65);
x_74 = 0;
x_75 = l_Lake_BuildTrace_nil;
x_76 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set_uint8(x_76, sizeof(void*)*2, x_74);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_72);
lean_ctor_set(x_77, 1, x_76);
x_48 = x_77;
x_49 = x_66;
goto block_64;
}
}
else
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_65);
if (x_78 == 0)
{
lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_65, 1);
x_80 = 0;
x_81 = l_Lake_BuildTrace_nil;
x_82 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set_uint8(x_82, sizeof(void*)*2, x_80);
lean_ctor_set(x_65, 1, x_82);
x_48 = x_65;
x_49 = x_66;
goto block_64;
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_83 = lean_ctor_get(x_65, 0);
x_84 = lean_ctor_get(x_65, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_65);
x_85 = 0;
x_86 = l_Lake_BuildTrace_nil;
x_87 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set_uint8(x_87, sizeof(void*)*2, x_85);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_83);
lean_ctor_set(x_88, 1, x_87);
x_48 = x_88;
x_49 = x_66;
goto block_64;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildLean___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildLean___spec__1(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildLean), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_nullFormat___rarg___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lake_LeanLib_modulesFacetConfig___closed__2;
x_2 = l_Lake_LeanLib_leanArtsFacetConfig___closed__1;
x_3 = l_Lake_instDataKindUnit;
x_4 = 1;
x_5 = l_Lake_LeanLib_leanArtsFacetConfig___closed__2;
x_6 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_4);
return x_6;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_LeanLib_leanArtsFacetConfig___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_ModuleFacet_fetch___rarg(x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lambda__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
lean_inc(x_4);
x_11 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___lambda__1), 8, 1);
lean_closure_set(x_11, 0, x_4);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 8);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(x_1);
x_16 = lean_apply_1(x_14, x_15);
x_17 = lean_array_size(x_16);
x_18 = 0;
x_19 = l_Array_mapMUnsafe_map___rarg(x_2, x_11, x_17, x_18, x_16);
x_20 = lean_apply_6(x_19, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = l_Array_append___rarg(x_3, x_25);
lean_dec(x_25);
lean_ctor_set(x_21, 0, x_26);
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
x_29 = l_Array_append___rarg(x_3, x_27);
lean_dec(x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_20, 0, x_30);
return x_20;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_dec(x_20);
x_32 = lean_ctor_get(x_21, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_34 = x_21;
} else {
 lean_dec_ref(x_21);
 x_34 = lean_box(0);
}
x_35 = l_Array_append___rarg(x_3, x_32);
lean_dec(x_32);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_31);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_20);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_20, 0);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_21);
if (x_40 == 0)
{
return x_20;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_21, 0);
x_42 = lean_ctor_get(x_21, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_21);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_20, 0, x_43);
return x_20;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_20, 1);
lean_inc(x_44);
lean_dec(x_20);
x_45 = lean_ctor_get(x_21, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_21, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_47 = x_21;
} else {
 lean_dec_ref(x_21);
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
lean_dec(x_3);
x_50 = !lean_is_exclusive(x_20);
if (x_50 == 0)
{
return x_20;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_20, 0);
x_52 = lean_ctor_get(x_20, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_20);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_array_push(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildStatic___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("export", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildStatic___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___lambda__3___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_276; lean_object* x_277; lean_object* x_293; lean_object* x_294; lean_object* x_318; lean_object* x_319; 
x_318 = lean_ctor_get(x_6, 0);
lean_inc(x_318);
lean_dec(x_6);
x_319 = lean_io_wait(x_318, x_12);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; 
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; uint8_t x_323; 
x_321 = lean_ctor_get(x_320, 1);
lean_inc(x_321);
x_322 = lean_ctor_get(x_319, 1);
lean_inc(x_322);
lean_dec(x_319);
x_323 = !lean_is_exclusive(x_320);
if (x_323 == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; uint8_t x_329; 
x_324 = lean_ctor_get(x_320, 0);
x_325 = lean_ctor_get(x_320, 1);
lean_dec(x_325);
x_326 = lean_ctor_get(x_321, 0);
lean_inc(x_326);
lean_dec(x_321);
x_327 = lean_array_get_size(x_326);
x_328 = lean_unsigned_to_nat(0u);
x_329 = lean_nat_dec_lt(x_328, x_327);
if (x_329 == 0)
{
lean_dec(x_327);
lean_dec(x_326);
lean_dec(x_5);
lean_ctor_set(x_320, 1, x_11);
x_293 = x_320;
x_294 = x_322;
goto block_317;
}
else
{
uint8_t x_330; 
x_330 = lean_nat_dec_le(x_327, x_327);
if (x_330 == 0)
{
lean_dec(x_327);
lean_dec(x_326);
lean_dec(x_5);
lean_ctor_set(x_320, 1, x_11);
x_293 = x_320;
x_294 = x_322;
goto block_317;
}
else
{
size_t x_331; size_t x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
lean_free_object(x_320);
x_331 = 0;
x_332 = lean_usize_of_nat(x_327);
lean_dec(x_327);
x_333 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__3;
x_334 = lean_box(0);
x_335 = l_Array_foldlMUnsafe_fold___rarg(x_5, x_333, x_326, x_331, x_332, x_334);
x_336 = lean_apply_2(x_335, x_11, x_322);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; 
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; uint8_t x_339; 
x_338 = lean_ctor_get(x_336, 1);
lean_inc(x_338);
lean_dec(x_336);
x_339 = !lean_is_exclusive(x_337);
if (x_339 == 0)
{
lean_object* x_340; 
x_340 = lean_ctor_get(x_337, 0);
lean_dec(x_340);
lean_ctor_set(x_337, 0, x_324);
x_293 = x_337;
x_294 = x_338;
goto block_317;
}
else
{
lean_object* x_341; lean_object* x_342; 
x_341 = lean_ctor_get(x_337, 1);
lean_inc(x_341);
lean_dec(x_337);
x_342 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_342, 0, x_324);
lean_ctor_set(x_342, 1, x_341);
x_293 = x_342;
x_294 = x_338;
goto block_317;
}
}
else
{
lean_object* x_343; uint8_t x_344; 
lean_dec(x_324);
x_343 = lean_ctor_get(x_336, 1);
lean_inc(x_343);
lean_dec(x_336);
x_344 = !lean_is_exclusive(x_337);
if (x_344 == 0)
{
x_293 = x_337;
x_294 = x_343;
goto block_317;
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_345 = lean_ctor_get(x_337, 0);
x_346 = lean_ctor_get(x_337, 1);
lean_inc(x_346);
lean_inc(x_345);
lean_dec(x_337);
x_347 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_347, 0, x_345);
lean_ctor_set(x_347, 1, x_346);
x_293 = x_347;
x_294 = x_343;
goto block_317;
}
}
}
else
{
uint8_t x_348; 
lean_dec(x_324);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_348 = !lean_is_exclusive(x_336);
if (x_348 == 0)
{
return x_336;
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_349 = lean_ctor_get(x_336, 0);
x_350 = lean_ctor_get(x_336, 1);
lean_inc(x_350);
lean_inc(x_349);
lean_dec(x_336);
x_351 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_351, 0, x_349);
lean_ctor_set(x_351, 1, x_350);
return x_351;
}
}
}
}
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; uint8_t x_356; 
x_352 = lean_ctor_get(x_320, 0);
lean_inc(x_352);
lean_dec(x_320);
x_353 = lean_ctor_get(x_321, 0);
lean_inc(x_353);
lean_dec(x_321);
x_354 = lean_array_get_size(x_353);
x_355 = lean_unsigned_to_nat(0u);
x_356 = lean_nat_dec_lt(x_355, x_354);
if (x_356 == 0)
{
lean_object* x_357; 
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_5);
x_357 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_357, 0, x_352);
lean_ctor_set(x_357, 1, x_11);
x_293 = x_357;
x_294 = x_322;
goto block_317;
}
else
{
uint8_t x_358; 
x_358 = lean_nat_dec_le(x_354, x_354);
if (x_358 == 0)
{
lean_object* x_359; 
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_5);
x_359 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_359, 0, x_352);
lean_ctor_set(x_359, 1, x_11);
x_293 = x_359;
x_294 = x_322;
goto block_317;
}
else
{
size_t x_360; size_t x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_360 = 0;
x_361 = lean_usize_of_nat(x_354);
lean_dec(x_354);
x_362 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__3;
x_363 = lean_box(0);
x_364 = l_Array_foldlMUnsafe_fold___rarg(x_5, x_362, x_353, x_360, x_361, x_363);
x_365 = lean_apply_2(x_364, x_11, x_322);
if (lean_obj_tag(x_365) == 0)
{
lean_object* x_366; 
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_367 = lean_ctor_get(x_365, 1);
lean_inc(x_367);
lean_dec(x_365);
x_368 = lean_ctor_get(x_366, 1);
lean_inc(x_368);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 x_369 = x_366;
} else {
 lean_dec_ref(x_366);
 x_369 = lean_box(0);
}
if (lean_is_scalar(x_369)) {
 x_370 = lean_alloc_ctor(0, 2, 0);
} else {
 x_370 = x_369;
}
lean_ctor_set(x_370, 0, x_352);
lean_ctor_set(x_370, 1, x_368);
x_293 = x_370;
x_294 = x_367;
goto block_317;
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
lean_dec(x_352);
x_371 = lean_ctor_get(x_365, 1);
lean_inc(x_371);
lean_dec(x_365);
x_372 = lean_ctor_get(x_366, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_366, 1);
lean_inc(x_373);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 x_374 = x_366;
} else {
 lean_dec_ref(x_366);
 x_374 = lean_box(0);
}
if (lean_is_scalar(x_374)) {
 x_375 = lean_alloc_ctor(1, 2, 0);
} else {
 x_375 = x_374;
}
lean_ctor_set(x_375, 0, x_372);
lean_ctor_set(x_375, 1, x_373);
x_293 = x_375;
x_294 = x_371;
goto block_317;
}
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
lean_dec(x_352);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_376 = lean_ctor_get(x_365, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_365, 1);
lean_inc(x_377);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 x_378 = x_365;
} else {
 lean_dec_ref(x_365);
 x_378 = lean_box(0);
}
if (lean_is_scalar(x_378)) {
 x_379 = lean_alloc_ctor(1, 2, 0);
} else {
 x_379 = x_378;
}
lean_ctor_set(x_379, 0, x_376);
lean_ctor_set(x_379, 1, x_377);
return x_379;
}
}
}
}
}
else
{
lean_object* x_380; lean_object* x_381; uint8_t x_382; 
x_380 = lean_ctor_get(x_320, 1);
lean_inc(x_380);
x_381 = lean_ctor_get(x_319, 1);
lean_inc(x_381);
lean_dec(x_319);
x_382 = !lean_is_exclusive(x_320);
if (x_382 == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; 
x_383 = lean_ctor_get(x_320, 0);
x_384 = lean_ctor_get(x_320, 1);
lean_dec(x_384);
x_385 = lean_ctor_get(x_380, 0);
lean_inc(x_385);
lean_dec(x_380);
x_386 = lean_array_get_size(x_385);
x_387 = lean_unsigned_to_nat(0u);
x_388 = lean_nat_dec_lt(x_387, x_386);
if (x_388 == 0)
{
lean_dec(x_386);
lean_dec(x_385);
lean_dec(x_5);
lean_ctor_set(x_320, 1, x_11);
x_293 = x_320;
x_294 = x_381;
goto block_317;
}
else
{
uint8_t x_389; 
x_389 = lean_nat_dec_le(x_386, x_386);
if (x_389 == 0)
{
lean_dec(x_386);
lean_dec(x_385);
lean_dec(x_5);
lean_ctor_set(x_320, 1, x_11);
x_293 = x_320;
x_294 = x_381;
goto block_317;
}
else
{
size_t x_390; size_t x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_free_object(x_320);
x_390 = 0;
x_391 = lean_usize_of_nat(x_386);
lean_dec(x_386);
x_392 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__3;
x_393 = lean_box(0);
x_394 = l_Array_foldlMUnsafe_fold___rarg(x_5, x_392, x_385, x_390, x_391, x_393);
x_395 = lean_apply_2(x_394, x_11, x_381);
if (lean_obj_tag(x_395) == 0)
{
lean_object* x_396; 
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; uint8_t x_398; 
x_397 = lean_ctor_get(x_395, 1);
lean_inc(x_397);
lean_dec(x_395);
x_398 = !lean_is_exclusive(x_396);
if (x_398 == 0)
{
lean_object* x_399; 
x_399 = lean_ctor_get(x_396, 0);
lean_dec(x_399);
lean_ctor_set_tag(x_396, 1);
lean_ctor_set(x_396, 0, x_383);
x_293 = x_396;
x_294 = x_397;
goto block_317;
}
else
{
lean_object* x_400; lean_object* x_401; 
x_400 = lean_ctor_get(x_396, 1);
lean_inc(x_400);
lean_dec(x_396);
x_401 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_401, 0, x_383);
lean_ctor_set(x_401, 1, x_400);
x_293 = x_401;
x_294 = x_397;
goto block_317;
}
}
else
{
lean_object* x_402; uint8_t x_403; 
lean_dec(x_383);
x_402 = lean_ctor_get(x_395, 1);
lean_inc(x_402);
lean_dec(x_395);
x_403 = !lean_is_exclusive(x_396);
if (x_403 == 0)
{
x_293 = x_396;
x_294 = x_402;
goto block_317;
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_404 = lean_ctor_get(x_396, 0);
x_405 = lean_ctor_get(x_396, 1);
lean_inc(x_405);
lean_inc(x_404);
lean_dec(x_396);
x_406 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_406, 0, x_404);
lean_ctor_set(x_406, 1, x_405);
x_293 = x_406;
x_294 = x_402;
goto block_317;
}
}
}
else
{
uint8_t x_407; 
lean_dec(x_383);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_407 = !lean_is_exclusive(x_395);
if (x_407 == 0)
{
return x_395;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_408 = lean_ctor_get(x_395, 0);
x_409 = lean_ctor_get(x_395, 1);
lean_inc(x_409);
lean_inc(x_408);
lean_dec(x_395);
x_410 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_410, 0, x_408);
lean_ctor_set(x_410, 1, x_409);
return x_410;
}
}
}
}
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; 
x_411 = lean_ctor_get(x_320, 0);
lean_inc(x_411);
lean_dec(x_320);
x_412 = lean_ctor_get(x_380, 0);
lean_inc(x_412);
lean_dec(x_380);
x_413 = lean_array_get_size(x_412);
x_414 = lean_unsigned_to_nat(0u);
x_415 = lean_nat_dec_lt(x_414, x_413);
if (x_415 == 0)
{
lean_object* x_416; 
lean_dec(x_413);
lean_dec(x_412);
lean_dec(x_5);
x_416 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_416, 0, x_411);
lean_ctor_set(x_416, 1, x_11);
x_293 = x_416;
x_294 = x_381;
goto block_317;
}
else
{
uint8_t x_417; 
x_417 = lean_nat_dec_le(x_413, x_413);
if (x_417 == 0)
{
lean_object* x_418; 
lean_dec(x_413);
lean_dec(x_412);
lean_dec(x_5);
x_418 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_418, 0, x_411);
lean_ctor_set(x_418, 1, x_11);
x_293 = x_418;
x_294 = x_381;
goto block_317;
}
else
{
size_t x_419; size_t x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_419 = 0;
x_420 = lean_usize_of_nat(x_413);
lean_dec(x_413);
x_421 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__3;
x_422 = lean_box(0);
x_423 = l_Array_foldlMUnsafe_fold___rarg(x_5, x_421, x_412, x_419, x_420, x_422);
x_424 = lean_apply_2(x_423, x_11, x_381);
if (lean_obj_tag(x_424) == 0)
{
lean_object* x_425; 
x_425 = lean_ctor_get(x_424, 0);
lean_inc(x_425);
if (lean_obj_tag(x_425) == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_426 = lean_ctor_get(x_424, 1);
lean_inc(x_426);
lean_dec(x_424);
x_427 = lean_ctor_get(x_425, 1);
lean_inc(x_427);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 x_428 = x_425;
} else {
 lean_dec_ref(x_425);
 x_428 = lean_box(0);
}
if (lean_is_scalar(x_428)) {
 x_429 = lean_alloc_ctor(1, 2, 0);
} else {
 x_429 = x_428;
 lean_ctor_set_tag(x_429, 1);
}
lean_ctor_set(x_429, 0, x_411);
lean_ctor_set(x_429, 1, x_427);
x_293 = x_429;
x_294 = x_426;
goto block_317;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; 
lean_dec(x_411);
x_430 = lean_ctor_get(x_424, 1);
lean_inc(x_430);
lean_dec(x_424);
x_431 = lean_ctor_get(x_425, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_425, 1);
lean_inc(x_432);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 x_433 = x_425;
} else {
 lean_dec_ref(x_425);
 x_433 = lean_box(0);
}
if (lean_is_scalar(x_433)) {
 x_434 = lean_alloc_ctor(1, 2, 0);
} else {
 x_434 = x_433;
}
lean_ctor_set(x_434, 0, x_431);
lean_ctor_set(x_434, 1, x_432);
x_293 = x_434;
x_294 = x_430;
goto block_317;
}
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
lean_dec(x_411);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_435 = lean_ctor_get(x_424, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_424, 1);
lean_inc(x_436);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 x_437 = x_424;
} else {
 lean_dec_ref(x_424);
 x_437 = lean_box(0);
}
if (lean_is_scalar(x_437)) {
 x_438 = lean_alloc_ctor(1, 2, 0);
} else {
 x_438 = x_437;
}
lean_ctor_set(x_438, 0, x_435);
lean_ctor_set(x_438, 1, x_436);
return x_438;
}
}
}
}
}
}
else
{
uint8_t x_439; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_439 = !lean_is_exclusive(x_319);
if (x_439 == 0)
{
return x_319;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_440 = lean_ctor_get(x_319, 0);
x_441 = lean_ctor_get(x_319, 1);
lean_inc(x_441);
lean_inc(x_440);
lean_dec(x_319);
x_442 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_442, 0, x_440);
lean_ctor_set(x_442, 1, x_441);
return x_442;
}
}
block_275:
{
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
x_18 = l_Lake_EquipT_instMonad___rarg(x_1);
x_147 = lean_box(x_4);
lean_inc(x_18);
x_148 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___lambda__2___boxed), 10, 2);
lean_closure_set(x_148, 0, x_147);
lean_closure_set(x_148, 1, x_18);
x_149 = lean_array_get_size(x_16);
x_150 = lean_unsigned_to_nat(0u);
x_151 = lean_nat_dec_lt(x_150, x_149);
if (x_151 == 0)
{
lean_object* x_152; 
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_16);
x_152 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2;
lean_ctor_set(x_13, 0, x_152);
x_19 = x_13;
x_20 = x_14;
goto block_146;
}
else
{
uint8_t x_153; 
x_153 = lean_nat_dec_le(x_149, x_149);
if (x_153 == 0)
{
lean_object* x_154; 
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_16);
x_154 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2;
lean_ctor_set(x_13, 0, x_154);
x_19 = x_13;
x_20 = x_14;
goto block_146;
}
else
{
size_t x_155; size_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_free_object(x_13);
x_155 = 0;
x_156 = lean_usize_of_nat(x_149);
lean_dec(x_149);
x_157 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2;
lean_inc(x_18);
x_158 = l_Array_foldlMUnsafe_fold___rarg(x_18, x_148, x_16, x_155, x_156, x_157);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_159 = lean_apply_6(x_158, x_7, x_8, x_9, x_10, x_17, x_14);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_19 = x_160;
x_20 = x_161;
goto block_146;
}
else
{
uint8_t x_162; 
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_162 = !lean_is_exclusive(x_159);
if (x_162 == 0)
{
return x_159;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_159, 0);
x_164 = lean_ctor_get(x_159, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_159);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
}
block_146:
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = l_Lake_instDataKindFilePath;
lean_inc(x_2);
x_24 = lean_alloc_closure((void*)(l_Lake_Target_fetchIn___rarg), 9, 2);
lean_closure_set(x_24, 0, x_23);
lean_closure_set(x_24, 1, x_2);
x_25 = lean_ctor_get(x_2, 3);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 6);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get(x_3, 0);
x_29 = lean_ctor_get(x_28, 6);
x_30 = l_Array_append___rarg(x_27, x_29);
x_31 = lean_array_size(x_30);
x_32 = 0;
x_33 = l_Array_mapMUnsafe_map___rarg(x_18, x_24, x_31, x_32, x_30);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_34 = lean_apply_6(x_33, x_7, x_8, x_9, x_10, x_22, x_20);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = lean_ctor_get(x_35, 1);
x_40 = l_Array_append___rarg(x_21, x_38);
lean_dec(x_38);
if (x_4 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_2, 1);
lean_inc(x_41);
lean_dec(x_2);
x_42 = lean_ctor_get(x_25, 6);
lean_inc(x_42);
x_43 = l_Lake_joinRelative(x_41, x_42);
lean_dec(x_42);
x_44 = lean_ctor_get(x_25, 8);
lean_inc(x_44);
lean_dec(x_25);
x_45 = l_Lake_joinRelative(x_43, x_44);
lean_dec(x_44);
x_46 = lean_ctor_get(x_3, 4);
x_47 = l_Lake_nameToStaticLib(x_46);
x_48 = l_Lake_joinRelative(x_45, x_47);
lean_dec(x_47);
x_49 = l_Lake_BuildTrace_nil;
x_50 = l_Lake_buildStaticLib(x_48, x_40, x_4, x_7, x_8, x_9, x_10, x_49, x_36);
lean_dec(x_40);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 0);
lean_ctor_set(x_35, 0, x_52);
lean_ctor_set(x_50, 0, x_35);
return x_50;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_50, 0);
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_50);
lean_ctor_set(x_35, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_35);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_free_object(x_35);
lean_dec(x_39);
x_56 = !lean_is_exclusive(x_50);
if (x_56 == 0)
{
return x_50;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_50, 0);
x_58 = lean_ctor_get(x_50, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_50);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_60 = lean_ctor_get(x_2, 1);
lean_inc(x_60);
lean_dec(x_2);
x_61 = lean_ctor_get(x_25, 6);
lean_inc(x_61);
x_62 = l_Lake_joinRelative(x_60, x_61);
lean_dec(x_61);
x_63 = lean_ctor_get(x_25, 8);
lean_inc(x_63);
lean_dec(x_25);
x_64 = l_Lake_joinRelative(x_62, x_63);
lean_dec(x_63);
x_65 = lean_ctor_get(x_3, 4);
x_66 = l_Lake_nameToStaticLib(x_65);
x_67 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__1;
x_68 = l_System_FilePath_addExtension(x_66, x_67);
x_69 = l_Lake_joinRelative(x_64, x_68);
lean_dec(x_68);
x_70 = l_Lake_BuildTrace_nil;
x_71 = l_Lake_buildStaticLib(x_69, x_40, x_4, x_7, x_8, x_9, x_10, x_70, x_36);
lean_dec(x_40);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_71, 0);
lean_ctor_set(x_35, 0, x_73);
lean_ctor_set(x_71, 0, x_35);
return x_71;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_71, 0);
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_71);
lean_ctor_set(x_35, 0, x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_35);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_free_object(x_35);
lean_dec(x_39);
x_77 = !lean_is_exclusive(x_71);
if (x_77 == 0)
{
return x_71;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_71, 0);
x_79 = lean_ctor_get(x_71, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_71);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_35, 0);
x_82 = lean_ctor_get(x_35, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_35);
x_83 = l_Array_append___rarg(x_21, x_81);
lean_dec(x_81);
if (x_4 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_84 = lean_ctor_get(x_2, 1);
lean_inc(x_84);
lean_dec(x_2);
x_85 = lean_ctor_get(x_25, 6);
lean_inc(x_85);
x_86 = l_Lake_joinRelative(x_84, x_85);
lean_dec(x_85);
x_87 = lean_ctor_get(x_25, 8);
lean_inc(x_87);
lean_dec(x_25);
x_88 = l_Lake_joinRelative(x_86, x_87);
lean_dec(x_87);
x_89 = lean_ctor_get(x_3, 4);
x_90 = l_Lake_nameToStaticLib(x_89);
x_91 = l_Lake_joinRelative(x_88, x_90);
lean_dec(x_90);
x_92 = l_Lake_BuildTrace_nil;
x_93 = l_Lake_buildStaticLib(x_91, x_83, x_4, x_7, x_8, x_9, x_10, x_92, x_36);
lean_dec(x_83);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
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
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_82);
if (lean_is_scalar(x_96)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_96;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_95);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_82);
x_99 = lean_ctor_get(x_93, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_93, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_101 = x_93;
} else {
 lean_dec_ref(x_93);
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
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_103 = lean_ctor_get(x_2, 1);
lean_inc(x_103);
lean_dec(x_2);
x_104 = lean_ctor_get(x_25, 6);
lean_inc(x_104);
x_105 = l_Lake_joinRelative(x_103, x_104);
lean_dec(x_104);
x_106 = lean_ctor_get(x_25, 8);
lean_inc(x_106);
lean_dec(x_25);
x_107 = l_Lake_joinRelative(x_105, x_106);
lean_dec(x_106);
x_108 = lean_ctor_get(x_3, 4);
x_109 = l_Lake_nameToStaticLib(x_108);
x_110 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__1;
x_111 = l_System_FilePath_addExtension(x_109, x_110);
x_112 = l_Lake_joinRelative(x_107, x_111);
lean_dec(x_111);
x_113 = l_Lake_BuildTrace_nil;
x_114 = l_Lake_buildStaticLib(x_112, x_83, x_4, x_7, x_8, x_9, x_10, x_113, x_36);
lean_dec(x_83);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
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
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_82);
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_116);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_82);
x_120 = lean_ctor_get(x_114, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_114, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_122 = x_114;
} else {
 lean_dec_ref(x_114);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_124 = !lean_is_exclusive(x_34);
if (x_124 == 0)
{
lean_object* x_125; uint8_t x_126; 
x_125 = lean_ctor_get(x_34, 0);
lean_dec(x_125);
x_126 = !lean_is_exclusive(x_35);
if (x_126 == 0)
{
return x_34;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_35, 0);
x_128 = lean_ctor_get(x_35, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_35);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
lean_ctor_set(x_34, 0, x_129);
return x_34;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_130 = lean_ctor_get(x_34, 1);
lean_inc(x_130);
lean_dec(x_34);
x_131 = lean_ctor_get(x_35, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_35, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_133 = x_35;
} else {
 lean_dec_ref(x_35);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_130);
return x_135;
}
}
}
else
{
uint8_t x_136; 
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_136 = !lean_is_exclusive(x_34);
if (x_136 == 0)
{
return x_34;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_34, 0);
x_138 = lean_ctor_get(x_34, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_34);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
else
{
uint8_t x_140; 
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_140 = !lean_is_exclusive(x_19);
if (x_140 == 0)
{
lean_object* x_141; 
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_19);
lean_ctor_set(x_141, 1, x_20);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_142 = lean_ctor_get(x_19, 0);
x_143 = lean_ctor_get(x_19, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_19);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_20);
return x_145;
}
}
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; 
x_166 = lean_ctor_get(x_13, 0);
x_167 = lean_ctor_get(x_13, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_13);
x_168 = l_Lake_EquipT_instMonad___rarg(x_1);
x_248 = lean_box(x_4);
lean_inc(x_168);
x_249 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___lambda__2___boxed), 10, 2);
lean_closure_set(x_249, 0, x_248);
lean_closure_set(x_249, 1, x_168);
x_250 = lean_array_get_size(x_166);
x_251 = lean_unsigned_to_nat(0u);
x_252 = lean_nat_dec_lt(x_251, x_250);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; 
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_166);
x_253 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2;
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_167);
x_169 = x_254;
x_170 = x_14;
goto block_247;
}
else
{
uint8_t x_255; 
x_255 = lean_nat_dec_le(x_250, x_250);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; 
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_166);
x_256 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2;
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_167);
x_169 = x_257;
x_170 = x_14;
goto block_247;
}
else
{
size_t x_258; size_t x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_258 = 0;
x_259 = lean_usize_of_nat(x_250);
lean_dec(x_250);
x_260 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2;
lean_inc(x_168);
x_261 = l_Array_foldlMUnsafe_fold___rarg(x_168, x_249, x_166, x_258, x_259, x_260);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_262 = lean_apply_6(x_261, x_7, x_8, x_9, x_10, x_167, x_14);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec(x_262);
x_169 = x_263;
x_170 = x_264;
goto block_247;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_168);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_265 = lean_ctor_get(x_262, 0);
lean_inc(x_265);
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
}
block_247:
{
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; size_t x_181; size_t x_182; lean_object* x_183; lean_object* x_184; 
x_171 = lean_ctor_get(x_169, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_169, 1);
lean_inc(x_172);
lean_dec(x_169);
x_173 = l_Lake_instDataKindFilePath;
lean_inc(x_2);
x_174 = lean_alloc_closure((void*)(l_Lake_Target_fetchIn___rarg), 9, 2);
lean_closure_set(x_174, 0, x_173);
lean_closure_set(x_174, 1, x_2);
x_175 = lean_ctor_get(x_2, 3);
lean_inc(x_175);
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
x_177 = lean_ctor_get(x_176, 6);
lean_inc(x_177);
lean_dec(x_176);
x_178 = lean_ctor_get(x_3, 0);
x_179 = lean_ctor_get(x_178, 6);
x_180 = l_Array_append___rarg(x_177, x_179);
x_181 = lean_array_size(x_180);
x_182 = 0;
x_183 = l_Array_mapMUnsafe_map___rarg(x_168, x_174, x_181, x_182, x_180);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_184 = lean_apply_6(x_183, x_7, x_8, x_9, x_10, x_172, x_170);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = lean_ctor_get(x_185, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_185, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_189 = x_185;
} else {
 lean_dec_ref(x_185);
 x_189 = lean_box(0);
}
x_190 = l_Array_append___rarg(x_171, x_187);
lean_dec(x_187);
if (x_4 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_191 = lean_ctor_get(x_2, 1);
lean_inc(x_191);
lean_dec(x_2);
x_192 = lean_ctor_get(x_175, 6);
lean_inc(x_192);
x_193 = l_Lake_joinRelative(x_191, x_192);
lean_dec(x_192);
x_194 = lean_ctor_get(x_175, 8);
lean_inc(x_194);
lean_dec(x_175);
x_195 = l_Lake_joinRelative(x_193, x_194);
lean_dec(x_194);
x_196 = lean_ctor_get(x_3, 4);
x_197 = l_Lake_nameToStaticLib(x_196);
x_198 = l_Lake_joinRelative(x_195, x_197);
lean_dec(x_197);
x_199 = l_Lake_BuildTrace_nil;
x_200 = l_Lake_buildStaticLib(x_198, x_190, x_4, x_7, x_8, x_9, x_10, x_199, x_186);
lean_dec(x_190);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_203 = x_200;
} else {
 lean_dec_ref(x_200);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_189;
}
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_188);
if (lean_is_scalar(x_203)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_203;
}
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_202);
return x_205;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_189);
lean_dec(x_188);
x_206 = lean_ctor_get(x_200, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_200, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_208 = x_200;
} else {
 lean_dec_ref(x_200);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(1, 2, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_207);
return x_209;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_210 = lean_ctor_get(x_2, 1);
lean_inc(x_210);
lean_dec(x_2);
x_211 = lean_ctor_get(x_175, 6);
lean_inc(x_211);
x_212 = l_Lake_joinRelative(x_210, x_211);
lean_dec(x_211);
x_213 = lean_ctor_get(x_175, 8);
lean_inc(x_213);
lean_dec(x_175);
x_214 = l_Lake_joinRelative(x_212, x_213);
lean_dec(x_213);
x_215 = lean_ctor_get(x_3, 4);
x_216 = l_Lake_nameToStaticLib(x_215);
x_217 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__1;
x_218 = l_System_FilePath_addExtension(x_216, x_217);
x_219 = l_Lake_joinRelative(x_214, x_218);
lean_dec(x_218);
x_220 = l_Lake_BuildTrace_nil;
x_221 = l_Lake_buildStaticLib(x_219, x_190, x_4, x_7, x_8, x_9, x_10, x_220, x_186);
lean_dec(x_190);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
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
if (lean_is_scalar(x_189)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_189;
}
lean_ctor_set(x_225, 0, x_222);
lean_ctor_set(x_225, 1, x_188);
if (lean_is_scalar(x_224)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_224;
}
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_223);
return x_226;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_189);
lean_dec(x_188);
x_227 = lean_ctor_get(x_221, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_221, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_229 = x_221;
} else {
 lean_dec_ref(x_221);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(1, 2, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_227);
lean_ctor_set(x_230, 1, x_228);
return x_230;
}
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_175);
lean_dec(x_171);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_231 = lean_ctor_get(x_184, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_232 = x_184;
} else {
 lean_dec_ref(x_184);
 x_232 = lean_box(0);
}
x_233 = lean_ctor_get(x_185, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_185, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_235 = x_185;
} else {
 lean_dec_ref(x_185);
 x_235 = lean_box(0);
}
if (lean_is_scalar(x_235)) {
 x_236 = lean_alloc_ctor(1, 2, 0);
} else {
 x_236 = x_235;
}
lean_ctor_set(x_236, 0, x_233);
lean_ctor_set(x_236, 1, x_234);
if (lean_is_scalar(x_232)) {
 x_237 = lean_alloc_ctor(0, 2, 0);
} else {
 x_237 = x_232;
}
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_231);
return x_237;
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_175);
lean_dec(x_171);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_238 = lean_ctor_get(x_184, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_184, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_240 = x_184;
} else {
 lean_dec_ref(x_184);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_241 = lean_alloc_ctor(1, 2, 0);
} else {
 x_241 = x_240;
}
lean_ctor_set(x_241, 0, x_238);
lean_ctor_set(x_241, 1, x_239);
return x_241;
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_168);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_242 = lean_ctor_get(x_169, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_169, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_244 = x_169;
} else {
 lean_dec_ref(x_169);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(1, 2, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_243);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_170);
return x_246;
}
}
}
}
else
{
uint8_t x_269; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_269 = !lean_is_exclusive(x_13);
if (x_269 == 0)
{
lean_object* x_270; 
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_13);
lean_ctor_set(x_270, 1, x_14);
return x_270;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_271 = lean_ctor_get(x_13, 0);
x_272 = lean_ctor_get(x_13, 1);
lean_inc(x_272);
lean_inc(x_271);
lean_dec(x_13);
x_273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_273, 0, x_271);
lean_ctor_set(x_273, 1, x_272);
x_274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_14);
return x_274;
}
}
}
block_292:
{
if (lean_obj_tag(x_276) == 0)
{
uint8_t x_278; 
x_278 = !lean_is_exclusive(x_276);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; 
x_279 = lean_ctor_get(x_276, 1);
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
lean_dec(x_279);
lean_ctor_set(x_276, 1, x_280);
x_13 = x_276;
x_14 = x_277;
goto block_275;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_281 = lean_ctor_get(x_276, 0);
x_282 = lean_ctor_get(x_276, 1);
lean_inc(x_282);
lean_inc(x_281);
lean_dec(x_276);
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
lean_dec(x_282);
x_284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_284, 0, x_281);
lean_ctor_set(x_284, 1, x_283);
x_13 = x_284;
x_14 = x_277;
goto block_275;
}
}
else
{
uint8_t x_285; 
x_285 = !lean_is_exclusive(x_276);
if (x_285 == 0)
{
lean_object* x_286; lean_object* x_287; 
x_286 = lean_ctor_get(x_276, 1);
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
lean_dec(x_286);
lean_ctor_set(x_276, 1, x_287);
x_13 = x_276;
x_14 = x_277;
goto block_275;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_288 = lean_ctor_get(x_276, 0);
x_289 = lean_ctor_get(x_276, 1);
lean_inc(x_289);
lean_inc(x_288);
lean_dec(x_276);
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
lean_dec(x_289);
x_291 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_291, 0, x_288);
lean_ctor_set(x_291, 1, x_290);
x_13 = x_291;
x_14 = x_277;
goto block_275;
}
}
}
block_317:
{
if (lean_obj_tag(x_293) == 0)
{
uint8_t x_295; 
x_295 = !lean_is_exclusive(x_293);
if (x_295 == 0)
{
lean_object* x_296; uint8_t x_297; lean_object* x_298; lean_object* x_299; 
x_296 = lean_ctor_get(x_293, 1);
x_297 = 0;
x_298 = l_Lake_BuildTrace_nil;
x_299 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_299, 0, x_296);
lean_ctor_set(x_299, 1, x_298);
lean_ctor_set_uint8(x_299, sizeof(void*)*2, x_297);
lean_ctor_set(x_293, 1, x_299);
x_276 = x_293;
x_277 = x_294;
goto block_292;
}
else
{
lean_object* x_300; lean_object* x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_300 = lean_ctor_get(x_293, 0);
x_301 = lean_ctor_get(x_293, 1);
lean_inc(x_301);
lean_inc(x_300);
lean_dec(x_293);
x_302 = 0;
x_303 = l_Lake_BuildTrace_nil;
x_304 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_304, 0, x_301);
lean_ctor_set(x_304, 1, x_303);
lean_ctor_set_uint8(x_304, sizeof(void*)*2, x_302);
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_300);
lean_ctor_set(x_305, 1, x_304);
x_276 = x_305;
x_277 = x_294;
goto block_292;
}
}
else
{
uint8_t x_306; 
x_306 = !lean_is_exclusive(x_293);
if (x_306 == 0)
{
lean_object* x_307; uint8_t x_308; lean_object* x_309; lean_object* x_310; 
x_307 = lean_ctor_get(x_293, 1);
x_308 = 0;
x_309 = l_Lake_BuildTrace_nil;
x_310 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_310, 0, x_307);
lean_ctor_set(x_310, 1, x_309);
lean_ctor_set_uint8(x_310, sizeof(void*)*2, x_308);
lean_ctor_set(x_293, 1, x_310);
x_276 = x_293;
x_277 = x_294;
goto block_292;
}
else
{
lean_object* x_311; lean_object* x_312; uint8_t x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_311 = lean_ctor_get(x_293, 0);
x_312 = lean_ctor_get(x_293, 1);
lean_inc(x_312);
lean_inc(x_311);
lean_dec(x_293);
x_313 = 0;
x_314 = l_Lake_BuildTrace_nil;
x_315 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_315, 0, x_312);
lean_ctor_set(x_315, 1, x_314);
lean_ctor_set_uint8(x_315, sizeof(void*)*2, x_313);
x_316 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_316, 0, x_311);
lean_ctor_set(x_316, 1, x_315);
x_276 = x_316;
x_277 = x_294;
goto block_292;
}
}
}
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildStatic___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instMonadBaseIO;
x_2 = l_Lake_EStateT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildStatic___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_LeanLib_recBuildStatic___closed__1;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildStatic___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_LeanLib_recBuildStatic___closed__2;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildStatic___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_LeanLib_recBuildStatic___closed__3;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildStatic___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":static", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildStatic___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" (without exports)", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildStatic___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" (with exports)", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_9 = l_Lake_LeanLib_recBuildStatic___closed__4;
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*1 + 3);
lean_dec(x_11);
x_13 = 2;
x_14 = l_Lake_instDecidableEqVerbosity(x_12, x_13);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
x_18 = 1;
x_19 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___spec__2___closed__1;
lean_inc(x_16);
x_20 = l_Lean_Name_toString(x_16, x_18, x_19);
x_21 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__1;
x_22 = lean_string_append(x_21, x_20);
lean_dec(x_20);
x_23 = l_Lake_LeanLib_recBuildStatic___closed__5;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_ctor_get(x_15, 0);
lean_inc(x_25);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_16);
x_27 = l_Lake_LeanLib_modulesFacetConfig___closed__2;
x_28 = l_Lake_LeanLib_modulesFacet;
x_29 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_1);
lean_ctor_set(x_29, 3, x_28);
x_30 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_30, 0, x_29);
lean_closure_set(x_30, 1, lean_box(0));
x_31 = l_Lake_LeanLib_recBuildStatic___closed__1;
x_32 = lean_box(x_2);
x_33 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___lambda__4___boxed), 12, 5);
lean_closure_set(x_33, 0, x_9);
lean_closure_set(x_33, 1, x_15);
lean_closure_set(x_33, 2, x_17);
lean_closure_set(x_33, 3, x_32);
lean_closure_set(x_33, 4, x_31);
x_34 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___rarg), 6, 5);
lean_closure_set(x_34, 0, x_10);
lean_closure_set(x_34, 1, lean_box(0));
lean_closure_set(x_34, 2, lean_box(0));
lean_closure_set(x_34, 3, x_30);
lean_closure_set(x_34, 4, x_33);
if (x_14 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_35 = lean_string_append(x_24, x_21);
x_36 = lean_string_append(x_35, x_21);
x_37 = l_Lake_instDataKindFilePath;
x_38 = 0;
x_39 = l_Lake_withRegisterJob___rarg(x_37, x_36, x_34, x_38, x_3, x_4, x_5, x_6, x_7, x_8);
return x_39;
}
else
{
if (x_2 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_40 = l_Lake_LeanLib_recBuildStatic___closed__6;
x_41 = lean_string_append(x_24, x_40);
x_42 = lean_string_append(x_41, x_21);
x_43 = l_Lake_instDataKindFilePath;
x_44 = 0;
x_45 = l_Lake_withRegisterJob___rarg(x_43, x_42, x_34, x_44, x_3, x_4, x_5, x_6, x_7, x_8);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; 
x_46 = l_Lake_LeanLib_recBuildStatic___closed__7;
x_47 = lean_string_append(x_24, x_46);
x_48 = lean_string_append(x_47, x_21);
x_49 = l_Lake_instDataKindFilePath;
x_50 = 0;
x_51 = l_Lake_withRegisterJob___rarg(x_49, x_48, x_34, x_50, x_3, x_4, x_5, x_6, x_7, x_8);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lake_LeanLib_recBuildStatic___lambda__2(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_LeanLib_recBuildStatic___lambda__3(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l_Lake_LeanLib_recBuildStatic___lambda__4(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lake_LeanLib_recBuildStatic(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_LeanLib_staticFacetConfig___spec__1(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lake_mkRelPathString(x_2);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = l_Lean_Json_compress(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 0;
x_9 = l_Lake_LeanLib_recBuildStatic(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_staticFacetConfig___lambda__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_stdFormat___at_Lake_LeanLib_staticFacetConfig___spec__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lake_LeanLib_modulesFacetConfig___closed__2;
x_2 = l_Lake_LeanLib_staticFacetConfig___closed__1;
x_3 = l_Lake_instDataKindFilePath;
x_4 = 1;
x_5 = l_Lake_LeanLib_staticFacetConfig___closed__2;
x_6 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_4);
return x_6;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_LeanLib_staticFacetConfig___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_LeanLib_staticFacetConfig___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_stdFormat___at_Lake_LeanLib_staticFacetConfig___spec__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 1;
x_9 = l_Lake_LeanLib_recBuildStatic(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_staticExportFacetConfig___lambda__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lake_LeanLib_modulesFacetConfig___closed__2;
x_2 = l_Lake_LeanLib_staticExportFacetConfig___closed__1;
x_3 = l_Lake_instDataKindFilePath;
x_4 = 1;
x_5 = l_Lake_LeanLib_staticFacetConfig___closed__2;
x_6 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_4);
return x_6;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_LeanLib_staticExportFacetConfig___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type mismtach in target '", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("': expected '", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_instDataKindDynlib;
x_2 = 1;
x_3 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___spec__2___closed__1;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', got ", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = 1;
lean_inc_n(x_2, 2);
x_10 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(x_1, x_2, x_2, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = l_Lake_instDataKindDynlib;
x_21 = lean_name_eq(x_19, x_20);
if (x_21 == 0)
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_18);
x_22 = l_Lean_Name_isAnonymous(x_19);
x_23 = l_Lake_PartialBuildKey_toString(x_2);
x_24 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__1;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__2;
x_27 = lean_string_append(x_25, x_26);
x_28 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__3;
x_29 = lean_string_append(x_27, x_28);
x_30 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__4;
x_31 = lean_string_append(x_29, x_30);
if (x_22 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_32 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___spec__2___closed__1;
x_33 = l_Lean_Name_toString(x_19, x_9, x_32);
x_34 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__5;
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
x_36 = lean_string_append(x_35, x_34);
x_37 = lean_string_append(x_31, x_36);
lean_dec(x_36);
x_38 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__1;
x_39 = lean_string_append(x_37, x_38);
x_40 = 3;
x_41 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_40);
x_42 = lean_array_get_size(x_16);
x_43 = lean_array_push(x_16, x_41);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_43);
lean_ctor_set(x_11, 0, x_42);
return x_10;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_19);
x_44 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__6;
x_45 = lean_string_append(x_31, x_44);
x_46 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__1;
x_47 = lean_string_append(x_45, x_46);
x_48 = 3;
x_49 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_48);
x_50 = lean_array_get_size(x_16);
x_51 = lean_array_push(x_16, x_49);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_51);
lean_ctor_set(x_11, 0, x_50);
return x_10;
}
}
else
{
lean_dec(x_19);
lean_dec(x_2);
lean_ctor_set(x_11, 0, x_18);
return x_10;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_11, 1);
lean_inc(x_52);
lean_dec(x_11);
x_53 = lean_ctor_get(x_12, 1);
lean_inc(x_53);
lean_dec(x_12);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
x_55 = l_Lake_instDataKindDynlib;
x_56 = lean_name_eq(x_54, x_55);
if (x_56 == 0)
{
uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_53);
x_57 = l_Lean_Name_isAnonymous(x_54);
x_58 = l_Lake_PartialBuildKey_toString(x_2);
x_59 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__1;
x_60 = lean_string_append(x_59, x_58);
lean_dec(x_58);
x_61 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__2;
x_62 = lean_string_append(x_60, x_61);
x_63 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__3;
x_64 = lean_string_append(x_62, x_63);
x_65 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__4;
x_66 = lean_string_append(x_64, x_65);
if (x_57 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_67 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___spec__2___closed__1;
x_68 = l_Lean_Name_toString(x_54, x_9, x_67);
x_69 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__5;
x_70 = lean_string_append(x_69, x_68);
lean_dec(x_68);
x_71 = lean_string_append(x_70, x_69);
x_72 = lean_string_append(x_66, x_71);
lean_dec(x_71);
x_73 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__1;
x_74 = lean_string_append(x_72, x_73);
x_75 = 3;
x_76 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*1, x_75);
x_77 = lean_array_get_size(x_52);
x_78 = lean_array_push(x_52, x_76);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_10, 0, x_79);
return x_10;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_54);
x_80 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__6;
x_81 = lean_string_append(x_66, x_80);
x_82 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__1;
x_83 = lean_string_append(x_81, x_82);
x_84 = 3;
x_85 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set_uint8(x_85, sizeof(void*)*1, x_84);
x_86 = lean_array_get_size(x_52);
x_87 = lean_array_push(x_52, x_85);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
lean_ctor_set(x_10, 0, x_88);
return x_10;
}
}
else
{
lean_object* x_89; 
lean_dec(x_54);
lean_dec(x_2);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_53);
lean_ctor_set(x_89, 1, x_52);
lean_ctor_set(x_10, 0, x_89);
return x_10;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_90 = lean_ctor_get(x_10, 1);
lean_inc(x_90);
lean_dec(x_10);
x_91 = lean_ctor_get(x_11, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_92 = x_11;
} else {
 lean_dec_ref(x_11);
 x_92 = lean_box(0);
}
x_93 = lean_ctor_get(x_12, 1);
lean_inc(x_93);
lean_dec(x_12);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
x_95 = l_Lake_instDataKindDynlib;
x_96 = lean_name_eq(x_94, x_95);
if (x_96 == 0)
{
uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_93);
x_97 = l_Lean_Name_isAnonymous(x_94);
x_98 = l_Lake_PartialBuildKey_toString(x_2);
x_99 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__1;
x_100 = lean_string_append(x_99, x_98);
lean_dec(x_98);
x_101 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__2;
x_102 = lean_string_append(x_100, x_101);
x_103 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__3;
x_104 = lean_string_append(x_102, x_103);
x_105 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__4;
x_106 = lean_string_append(x_104, x_105);
if (x_97 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_107 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___spec__2___closed__1;
x_108 = l_Lean_Name_toString(x_94, x_9, x_107);
x_109 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__5;
x_110 = lean_string_append(x_109, x_108);
lean_dec(x_108);
x_111 = lean_string_append(x_110, x_109);
x_112 = lean_string_append(x_106, x_111);
lean_dec(x_111);
x_113 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__1;
x_114 = lean_string_append(x_112, x_113);
x_115 = 3;
x_116 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set_uint8(x_116, sizeof(void*)*1, x_115);
x_117 = lean_array_get_size(x_91);
x_118 = lean_array_push(x_91, x_116);
if (lean_is_scalar(x_92)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_92;
 lean_ctor_set_tag(x_119, 1);
}
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_90);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_94);
x_121 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__6;
x_122 = lean_string_append(x_106, x_121);
x_123 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__1;
x_124 = lean_string_append(x_122, x_123);
x_125 = 3;
x_126 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set_uint8(x_126, sizeof(void*)*1, x_125);
x_127 = lean_array_get_size(x_91);
x_128 = lean_array_push(x_91, x_126);
if (lean_is_scalar(x_92)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_92;
 lean_ctor_set_tag(x_129, 1);
}
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_90);
return x_130;
}
}
else
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_94);
lean_dec(x_2);
if (lean_is_scalar(x_92)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_92;
}
lean_ctor_set(x_131, 0, x_93);
lean_ctor_set(x_131, 1, x_91);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_90);
return x_132;
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_2);
x_133 = !lean_is_exclusive(x_10);
if (x_133 == 0)
{
lean_object* x_134; uint8_t x_135; 
x_134 = lean_ctor_get(x_10, 0);
lean_dec(x_134);
x_135 = !lean_is_exclusive(x_11);
if (x_135 == 0)
{
return x_10;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_11, 0);
x_137 = lean_ctor_get(x_11, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_11);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
lean_ctor_set(x_10, 0, x_138);
return x_10;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_139 = lean_ctor_get(x_10, 1);
lean_inc(x_139);
lean_dec(x_10);
x_140 = lean_ctor_get(x_11, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_11, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_142 = x_11;
} else {
 lean_dec_ref(x_11);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_141);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_139);
return x_144;
}
}
}
else
{
uint8_t x_145; 
lean_dec(x_2);
x_145 = !lean_is_exclusive(x_10);
if (x_145 == 0)
{
return x_10;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_10, 0);
x_147 = lean_ctor_get(x_10, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_10);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_array_uget(x_1, x_2);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lake_ExternLib_keyword;
x_18 = l_Lake_ExternLib_dynlibFacet;
x_19 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_12);
lean_ctor_set(x_19, 3, x_18);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = lean_apply_6(x_5, x_19, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_array_push(x_4, x_23);
x_26 = 1;
x_27 = lean_usize_add(x_2, x_26);
x_2 = x_27;
x_4 = x_25;
x_9 = x_24;
x_10 = x_22;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_20, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_21);
if (x_31 == 0)
{
return x_20;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_21, 0);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_21);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_20, 0, x_34);
return x_20;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
lean_dec(x_20);
x_36 = lean_ctor_get(x_21, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_38 = x_21;
} else {
 lean_dec_ref(x_21);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_20);
if (x_41 == 0)
{
return x_20;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_20, 0);
x_43 = lean_ctor_get(x_20, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_20);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_4);
lean_ctor_set(x_45, 1, x_9);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_10);
return x_46;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_5, x_6);
if (x_8 == 0)
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_array_uget(x_4, x_5);
x_10 = 1;
x_11 = lean_usize_add(x_5, x_10);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 3);
lean_inc(x_14);
lean_dec(x_9);
x_15 = l_Lake_ExternLib_keyword;
x_16 = lean_name_eq(x_13, x_15);
lean_dec(x_13);
if (x_16 == 0)
{
lean_dec(x_14);
lean_dec(x_12);
x_5 = x_11;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_inc(x_2);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_12);
lean_ctor_set(x_18, 2, x_14);
x_19 = lean_array_push(x_7, x_18);
x_5 = x_11;
x_7 = x_19;
goto _start;
}
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_5, x_6);
if (x_8 == 0)
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_array_uget(x_4, x_5);
x_10 = 1;
x_11 = lean_usize_add(x_5, x_10);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 3);
lean_inc(x_14);
lean_dec(x_9);
x_15 = l_Lake_ExternLib_keyword;
x_16 = lean_name_eq(x_13, x_15);
lean_dec(x_13);
if (x_16 == 0)
{
lean_dec(x_14);
lean_dec(x_12);
x_5 = x_11;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_inc(x_2);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_12);
lean_ctor_set(x_18, 2, x_14);
x_19 = lean_array_push(x_7, x_18);
x_5 = x_11;
x_7 = x_19;
goto _start;
}
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_3, x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_uget(x_2, x_3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_14 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1(x_1, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_array_push(x_5, x_17);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_5 = x_19;
x_10 = x_18;
x_11 = x_16;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_14, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
return x_14;
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
lean_ctor_set(x_14, 0, x_28);
return x_14;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_dec(x_14);
x_30 = lean_ctor_get(x_15, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_32 = x_15;
} else {
 lean_dec_ref(x_15);
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
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_5);
lean_ctor_set(x_39, 1, x_10);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_11);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_5, x_6);
if (x_8 == 0)
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_array_uget(x_4, x_5);
x_10 = 1;
x_11 = lean_usize_add(x_5, x_10);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 3);
lean_inc(x_14);
lean_dec(x_9);
x_15 = l_Lake_ExternLib_keyword;
x_16 = lean_name_eq(x_13, x_15);
lean_dec(x_13);
if (x_16 == 0)
{
lean_dec(x_14);
lean_dec(x_12);
x_5 = x_11;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_inc(x_2);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_12);
lean_ctor_set(x_18, 2, x_14);
x_19 = lean_array_push(x_7, x_18);
x_5 = x_11;
x_7 = x_19;
goto _start;
}
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_3, x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_array_uget(x_2, x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
x_20 = l_Lean_NameSet_contains(x_16, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
lean_inc(x_19);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
x_23 = l_Lake_LeanLib_sharedFacet;
lean_inc(x_1);
x_24 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_1);
lean_ctor_set(x_24, 2, x_14);
lean_ctor_set(x_24, 3, x_23);
lean_inc(x_6);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_25 = lean_apply_6(x_6, x_24, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_array_push(x_17, x_28);
x_31 = lean_box(0);
x_32 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_16, x_19, x_31);
lean_ctor_set(x_5, 1, x_30);
lean_ctor_set(x_5, 0, x_32);
x_33 = 1;
x_34 = lean_usize_add(x_3, x_33);
x_3 = x_34;
x_10 = x_29;
x_11 = x_27;
goto _start;
}
else
{
uint8_t x_36; 
lean_dec(x_19);
lean_free_object(x_5);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_25);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_25, 0);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_26);
if (x_38 == 0)
{
return x_25;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_26, 0);
x_40 = lean_ctor_get(x_26, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_26);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_25, 0, x_41);
return x_25;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_25, 1);
lean_inc(x_42);
lean_dec(x_25);
x_43 = lean_ctor_get(x_26, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_26, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_45 = x_26;
} else {
 lean_dec_ref(x_26);
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
else
{
uint8_t x_48; 
lean_dec(x_19);
lean_free_object(x_5);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_25);
if (x_48 == 0)
{
return x_25;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_25, 0);
x_50 = lean_ctor_get(x_25, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_25);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
size_t x_52; size_t x_53; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_14);
x_52 = 1;
x_53 = lean_usize_add(x_3, x_52);
x_3 = x_53;
goto _start;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_55 = lean_ctor_get(x_5, 0);
x_56 = lean_ctor_get(x_5, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_5);
x_57 = lean_ctor_get(x_14, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_14, 1);
lean_inc(x_58);
x_59 = l_Lean_NameSet_contains(x_55, x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
lean_dec(x_57);
lean_inc(x_58);
x_61 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
x_62 = l_Lake_LeanLib_sharedFacet;
lean_inc(x_1);
x_63 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_1);
lean_ctor_set(x_63, 2, x_14);
lean_ctor_set(x_63, 3, x_62);
lean_inc(x_6);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_64 = lean_apply_6(x_6, x_63, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; 
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
x_69 = lean_array_push(x_56, x_67);
x_70 = lean_box(0);
x_71 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_55, x_58, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
x_73 = 1;
x_74 = lean_usize_add(x_3, x_73);
x_3 = x_74;
x_5 = x_72;
x_10 = x_68;
x_11 = x_66;
goto _start;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_76 = lean_ctor_get(x_64, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_77 = x_64;
} else {
 lean_dec_ref(x_64);
 x_77 = lean_box(0);
}
x_78 = lean_ctor_get(x_65, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_65, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_80 = x_65;
} else {
 lean_dec_ref(x_65);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
if (lean_is_scalar(x_77)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_77;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_76);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_83 = lean_ctor_get(x_64, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_64, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_85 = x_64;
} else {
 lean_dec_ref(x_64);
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
else
{
lean_object* x_87; size_t x_88; size_t x_89; 
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_14);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_55);
lean_ctor_set(x_87, 1, x_56);
x_88 = 1;
x_89 = lean_usize_add(x_3, x_88);
x_3 = x_89;
x_5 = x_87;
goto _start;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_5);
lean_ctor_set(x_91, 1, x_10);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_11);
return x_92;
}
}
}
static lean_object* _init_l_Lake_OrdHashSet_insert___at_Lake_LeanLib_recBuildShared___spec__9___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instHashableModule___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_OrdHashSet_insert___at_Lake_LeanLib_recBuildShared___spec__9___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instBEqModule___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at_Lake_LeanLib_recBuildShared___spec__9(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; uint8_t x_22; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
x_9 = l_Lean_Name_hash___override(x_8);
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
x_21 = lean_array_uget(x_6, x_20);
x_22 = l_Std_DHashMap_Internal_AssocList_contains___at_Lake_LeanLib_recCollectLocalModules_go___spec__1(x_2, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_dec(x_1);
lean_inc(x_2);
x_24 = lean_array_push(x_23, x_2);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_5, x_25);
lean_dec(x_5);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_21);
x_29 = lean_array_uset(x_6, x_20, x_28);
x_30 = lean_unsigned_to_nat(4u);
x_31 = lean_nat_mul(x_26, x_30);
x_32 = lean_unsigned_to_nat(3u);
x_33 = lean_nat_div(x_31, x_32);
lean_dec(x_31);
x_34 = lean_array_get_size(x_29);
x_35 = lean_nat_dec_le(x_33, x_34);
lean_dec(x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_LeanLib_recCollectLocalModules_go___spec__3(x_29);
lean_ctor_set(x_3, 1, x_36);
lean_ctor_set(x_3, 0, x_26);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_3);
lean_ctor_set(x_37, 1, x_24);
return x_37;
}
else
{
lean_object* x_38; 
lean_ctor_set(x_3, 1, x_29);
lean_ctor_set(x_3, 0, x_26);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_3);
lean_ctor_set(x_38, 1, x_24);
return x_38;
}
}
else
{
lean_dec(x_21);
lean_free_object(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_1;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; size_t x_50; size_t x_51; size_t x_52; size_t x_53; size_t x_54; lean_object* x_55; uint8_t x_56; 
x_39 = lean_ctor_get(x_3, 0);
x_40 = lean_ctor_get(x_3, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_3);
x_41 = lean_array_get_size(x_40);
x_42 = lean_ctor_get(x_2, 2);
lean_inc(x_42);
x_43 = l_Lean_Name_hash___override(x_42);
lean_dec(x_42);
x_44 = 32;
x_45 = lean_uint64_shift_right(x_43, x_44);
x_46 = lean_uint64_xor(x_43, x_45);
x_47 = 16;
x_48 = lean_uint64_shift_right(x_46, x_47);
x_49 = lean_uint64_xor(x_46, x_48);
x_50 = lean_uint64_to_usize(x_49);
x_51 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_52 = 1;
x_53 = lean_usize_sub(x_51, x_52);
x_54 = lean_usize_land(x_50, x_53);
x_55 = lean_array_uget(x_40, x_54);
x_56 = l_Std_DHashMap_Internal_AssocList_contains___at_Lake_LeanLib_recCollectLocalModules_go___spec__1(x_2, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_57 = lean_ctor_get(x_1, 1);
lean_inc(x_57);
lean_dec(x_1);
lean_inc(x_2);
x_58 = lean_array_push(x_57, x_2);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_add(x_39, x_59);
lean_dec(x_39);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_62, 0, x_2);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_62, 2, x_55);
x_63 = lean_array_uset(x_40, x_54, x_62);
x_64 = lean_unsigned_to_nat(4u);
x_65 = lean_nat_mul(x_60, x_64);
x_66 = lean_unsigned_to_nat(3u);
x_67 = lean_nat_div(x_65, x_66);
lean_dec(x_65);
x_68 = lean_array_get_size(x_63);
x_69 = lean_nat_dec_le(x_67, x_68);
lean_dec(x_68);
lean_dec(x_67);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_LeanLib_recCollectLocalModules_go___spec__3(x_63);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_60);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_58);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_60);
lean_ctor_set(x_73, 1, x_63);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_58);
return x_74;
}
}
else
{
lean_dec(x_55);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_2);
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__10(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lake_OrdHashSet_insert___at_Lake_LeanLib_recBuildShared___spec__9(x_4, x_6);
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
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at_Lake_LeanLib_recBuildShared___spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_3, x_3);
if (x_6 == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__10(x_2, x_7, x_8, x_1);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__11(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_25; lean_object* x_26; lean_object* x_39; lean_object* x_40; lean_object* x_56; lean_object* x_57; uint8_t x_81; 
x_81 = lean_usize_dec_eq(x_2, x_3);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_82 = lean_array_uget(x_1, x_2);
x_83 = lean_ctor_get(x_82, 2);
lean_inc(x_83);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = l_Lake_Module_keyword;
x_86 = l_Lake_Module_transImportsFacet;
x_87 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
lean_ctor_set(x_87, 2, x_82);
lean_ctor_set(x_87, 3, x_86);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_88 = lean_apply_6(x_5, x_87, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_dec(x_89);
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_io_wait(x_93, x_90);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_dec(x_94);
x_98 = !lean_is_exclusive(x_95);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_99 = lean_ctor_get(x_95, 0);
x_100 = lean_ctor_get(x_95, 1);
lean_dec(x_100);
x_101 = lean_ctor_get(x_96, 0);
lean_inc(x_101);
lean_dec(x_96);
x_102 = lean_array_get_size(x_101);
x_103 = lean_unsigned_to_nat(0u);
x_104 = lean_nat_dec_lt(x_103, x_102);
if (x_104 == 0)
{
lean_dec(x_102);
lean_dec(x_101);
lean_ctor_set(x_95, 1, x_92);
x_56 = x_95;
x_57 = x_97;
goto block_80;
}
else
{
uint8_t x_105; 
x_105 = lean_nat_dec_le(x_102, x_102);
if (x_105 == 0)
{
lean_dec(x_102);
lean_dec(x_101);
lean_ctor_set(x_95, 1, x_92);
x_56 = x_95;
x_57 = x_97;
goto block_80;
}
else
{
size_t x_106; size_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
lean_free_object(x_95);
x_106 = 0;
x_107 = lean_usize_of_nat(x_102);
lean_dec(x_102);
x_108 = lean_box(0);
x_109 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_101, x_106, x_107, x_108, x_92, x_97);
lean_dec(x_101);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = !lean_is_exclusive(x_110);
if (x_112 == 0)
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_110, 0);
lean_dec(x_113);
lean_ctor_set(x_110, 0, x_99);
x_56 = x_110;
x_57 = x_111;
goto block_80;
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_110, 1);
lean_inc(x_114);
lean_dec(x_110);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_99);
lean_ctor_set(x_115, 1, x_114);
x_56 = x_115;
x_57 = x_111;
goto block_80;
}
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_116 = lean_ctor_get(x_95, 0);
lean_inc(x_116);
lean_dec(x_95);
x_117 = lean_ctor_get(x_96, 0);
lean_inc(x_117);
lean_dec(x_96);
x_118 = lean_array_get_size(x_117);
x_119 = lean_unsigned_to_nat(0u);
x_120 = lean_nat_dec_lt(x_119, x_118);
if (x_120 == 0)
{
lean_object* x_121; 
lean_dec(x_118);
lean_dec(x_117);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_116);
lean_ctor_set(x_121, 1, x_92);
x_56 = x_121;
x_57 = x_97;
goto block_80;
}
else
{
uint8_t x_122; 
x_122 = lean_nat_dec_le(x_118, x_118);
if (x_122 == 0)
{
lean_object* x_123; 
lean_dec(x_118);
lean_dec(x_117);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_116);
lean_ctor_set(x_123, 1, x_92);
x_56 = x_123;
x_57 = x_97;
goto block_80;
}
else
{
size_t x_124; size_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_124 = 0;
x_125 = lean_usize_of_nat(x_118);
lean_dec(x_118);
x_126 = lean_box(0);
x_127 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_117, x_124, x_125, x_126, x_92, x_97);
lean_dec(x_117);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_131 = x_128;
} else {
 lean_dec_ref(x_128);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_116);
lean_ctor_set(x_132, 1, x_130);
x_56 = x_132;
x_57 = x_129;
goto block_80;
}
}
}
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_133 = lean_ctor_get(x_95, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_94, 1);
lean_inc(x_134);
lean_dec(x_94);
x_135 = !lean_is_exclusive(x_95);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_136 = lean_ctor_get(x_95, 0);
x_137 = lean_ctor_get(x_95, 1);
lean_dec(x_137);
x_138 = lean_ctor_get(x_133, 0);
lean_inc(x_138);
lean_dec(x_133);
x_139 = lean_array_get_size(x_138);
x_140 = lean_unsigned_to_nat(0u);
x_141 = lean_nat_dec_lt(x_140, x_139);
if (x_141 == 0)
{
lean_dec(x_139);
lean_dec(x_138);
lean_ctor_set(x_95, 1, x_92);
x_56 = x_95;
x_57 = x_134;
goto block_80;
}
else
{
uint8_t x_142; 
x_142 = lean_nat_dec_le(x_139, x_139);
if (x_142 == 0)
{
lean_dec(x_139);
lean_dec(x_138);
lean_ctor_set(x_95, 1, x_92);
x_56 = x_95;
x_57 = x_134;
goto block_80;
}
else
{
size_t x_143; size_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
lean_free_object(x_95);
x_143 = 0;
x_144 = lean_usize_of_nat(x_139);
lean_dec(x_139);
x_145 = lean_box(0);
x_146 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_138, x_143, x_144, x_145, x_92, x_134);
lean_dec(x_138);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = !lean_is_exclusive(x_147);
if (x_149 == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_147, 0);
lean_dec(x_150);
lean_ctor_set_tag(x_147, 1);
lean_ctor_set(x_147, 0, x_136);
x_56 = x_147;
x_57 = x_148;
goto block_80;
}
else
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_147, 1);
lean_inc(x_151);
lean_dec(x_147);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_136);
lean_ctor_set(x_152, 1, x_151);
x_56 = x_152;
x_57 = x_148;
goto block_80;
}
}
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_153 = lean_ctor_get(x_95, 0);
lean_inc(x_153);
lean_dec(x_95);
x_154 = lean_ctor_get(x_133, 0);
lean_inc(x_154);
lean_dec(x_133);
x_155 = lean_array_get_size(x_154);
x_156 = lean_unsigned_to_nat(0u);
x_157 = lean_nat_dec_lt(x_156, x_155);
if (x_157 == 0)
{
lean_object* x_158; 
lean_dec(x_155);
lean_dec(x_154);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_153);
lean_ctor_set(x_158, 1, x_92);
x_56 = x_158;
x_57 = x_134;
goto block_80;
}
else
{
uint8_t x_159; 
x_159 = lean_nat_dec_le(x_155, x_155);
if (x_159 == 0)
{
lean_object* x_160; 
lean_dec(x_155);
lean_dec(x_154);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_153);
lean_ctor_set(x_160, 1, x_92);
x_56 = x_160;
x_57 = x_134;
goto block_80;
}
else
{
size_t x_161; size_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_161 = 0;
x_162 = lean_usize_of_nat(x_155);
lean_dec(x_155);
x_163 = lean_box(0);
x_164 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_154, x_161, x_162, x_163, x_92, x_134);
lean_dec(x_154);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_168 = x_165;
} else {
 lean_dec_ref(x_165);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
 lean_ctor_set_tag(x_169, 1);
}
lean_ctor_set(x_169, 0, x_153);
lean_ctor_set(x_169, 1, x_167);
x_56 = x_169;
x_57 = x_166;
goto block_80;
}
}
}
}
}
else
{
uint8_t x_170; 
lean_dec(x_92);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_170 = !lean_is_exclusive(x_94);
if (x_170 == 0)
{
return x_94;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_94, 0);
x_172 = lean_ctor_get(x_94, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_94);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
}
else
{
lean_object* x_174; uint8_t x_175; 
lean_dec(x_4);
x_174 = lean_ctor_get(x_88, 1);
lean_inc(x_174);
lean_dec(x_88);
x_175 = !lean_is_exclusive(x_89);
if (x_175 == 0)
{
x_11 = x_89;
x_12 = x_174;
goto block_24;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_89, 0);
x_177 = lean_ctor_get(x_89, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_89);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
x_11 = x_178;
x_12 = x_174;
goto block_24;
}
}
}
else
{
uint8_t x_179; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_179 = !lean_is_exclusive(x_88);
if (x_179 == 0)
{
return x_88;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_88, 0);
x_181 = lean_ctor_get(x_88, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_88);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
}
}
else
{
lean_object* x_183; lean_object* x_184; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_4);
lean_ctor_set(x_183, 1, x_9);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_10);
return x_184;
}
block_24:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_2 = x_16;
x_4 = x_13;
x_9 = x_14;
x_10 = x_12;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_12);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_12);
return x_23;
}
}
}
block_38:
{
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 0);
x_29 = l_Lake_OrdHashSet_appendArray___at_Lake_LeanLib_recBuildShared___spec__8(x_4, x_28);
lean_dec(x_28);
lean_ctor_set(x_25, 0, x_29);
x_11 = x_25;
x_12 = x_26;
goto block_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_32 = l_Lake_OrdHashSet_appendArray___at_Lake_LeanLib_recBuildShared___spec__8(x_4, x_30);
lean_dec(x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_11 = x_33;
x_12 = x_26;
goto block_24;
}
}
else
{
uint8_t x_34; 
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
x_11 = x_25;
x_12 = x_26;
goto block_24;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_ctor_get(x_25, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_25);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_11 = x_37;
x_12 = x_26;
goto block_24;
}
}
}
block_55:
{
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 1);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec(x_42);
lean_ctor_set(x_39, 1, x_43);
x_25 = x_39;
x_26 = x_40;
goto block_38;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_39, 0);
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_39);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_46);
x_25 = x_47;
x_26 = x_40;
goto block_38;
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_39);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_39, 1);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec(x_49);
lean_ctor_set(x_39, 1, x_50);
x_25 = x_39;
x_26 = x_40;
goto block_38;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_39, 0);
x_52 = lean_ctor_get(x_39, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_39);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_53);
x_25 = x_54;
x_26 = x_40;
goto block_38;
}
}
}
block_80:
{
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_56);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_56, 1);
x_60 = 0;
x_61 = l_Lake_BuildTrace_nil;
x_62 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*2, x_60);
lean_ctor_set(x_56, 1, x_62);
x_39 = x_56;
x_40 = x_57;
goto block_55;
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_56, 0);
x_64 = lean_ctor_get(x_56, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_56);
x_65 = 0;
x_66 = l_Lake_BuildTrace_nil;
x_67 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set_uint8(x_67, sizeof(void*)*2, x_65);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_63);
lean_ctor_set(x_68, 1, x_67);
x_39 = x_68;
x_40 = x_57;
goto block_55;
}
}
else
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_56);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_56, 1);
x_71 = 0;
x_72 = l_Lake_BuildTrace_nil;
x_73 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set_uint8(x_73, sizeof(void*)*2, x_71);
lean_ctor_set(x_56, 1, x_73);
x_39 = x_56;
x_40 = x_57;
goto block_55;
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_74 = lean_ctor_get(x_56, 0);
x_75 = lean_ctor_get(x_56, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_56);
x_76 = 0;
x_77 = l_Lake_BuildTrace_nil;
x_78 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_77);
lean_ctor_set_uint8(x_78, sizeof(void*)*2, x_76);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_74);
lean_ctor_set(x_79, 1, x_78);
x_39 = x_79;
x_40 = x_57;
goto block_55;
}
}
}
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__12___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_instDataKindFilePath;
x_2 = 1;
x_3 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___spec__2___closed__1;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = 1;
lean_inc_n(x_2, 2);
x_10 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(x_1, x_2, x_2, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = l_Lake_instDataKindFilePath;
x_21 = lean_name_eq(x_19, x_20);
if (x_21 == 0)
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_18);
x_22 = l_Lean_Name_isAnonymous(x_19);
x_23 = l_Lake_PartialBuildKey_toString(x_2);
x_24 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__1;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__2;
x_27 = lean_string_append(x_25, x_26);
x_28 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__12___closed__1;
x_29 = lean_string_append(x_27, x_28);
x_30 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__4;
x_31 = lean_string_append(x_29, x_30);
if (x_22 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_32 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___spec__2___closed__1;
x_33 = l_Lean_Name_toString(x_19, x_9, x_32);
x_34 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__5;
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
x_36 = lean_string_append(x_35, x_34);
x_37 = lean_string_append(x_31, x_36);
lean_dec(x_36);
x_38 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__1;
x_39 = lean_string_append(x_37, x_38);
x_40 = 3;
x_41 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_40);
x_42 = lean_array_get_size(x_16);
x_43 = lean_array_push(x_16, x_41);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_43);
lean_ctor_set(x_11, 0, x_42);
return x_10;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_19);
x_44 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__6;
x_45 = lean_string_append(x_31, x_44);
x_46 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__1;
x_47 = lean_string_append(x_45, x_46);
x_48 = 3;
x_49 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_48);
x_50 = lean_array_get_size(x_16);
x_51 = lean_array_push(x_16, x_49);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_51);
lean_ctor_set(x_11, 0, x_50);
return x_10;
}
}
else
{
lean_dec(x_19);
lean_dec(x_2);
lean_ctor_set(x_11, 0, x_18);
return x_10;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_11, 1);
lean_inc(x_52);
lean_dec(x_11);
x_53 = lean_ctor_get(x_12, 1);
lean_inc(x_53);
lean_dec(x_12);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
x_55 = l_Lake_instDataKindFilePath;
x_56 = lean_name_eq(x_54, x_55);
if (x_56 == 0)
{
uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_53);
x_57 = l_Lean_Name_isAnonymous(x_54);
x_58 = l_Lake_PartialBuildKey_toString(x_2);
x_59 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__1;
x_60 = lean_string_append(x_59, x_58);
lean_dec(x_58);
x_61 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__2;
x_62 = lean_string_append(x_60, x_61);
x_63 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__12___closed__1;
x_64 = lean_string_append(x_62, x_63);
x_65 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__4;
x_66 = lean_string_append(x_64, x_65);
if (x_57 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_67 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___spec__2___closed__1;
x_68 = l_Lean_Name_toString(x_54, x_9, x_67);
x_69 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__5;
x_70 = lean_string_append(x_69, x_68);
lean_dec(x_68);
x_71 = lean_string_append(x_70, x_69);
x_72 = lean_string_append(x_66, x_71);
lean_dec(x_71);
x_73 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__1;
x_74 = lean_string_append(x_72, x_73);
x_75 = 3;
x_76 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*1, x_75);
x_77 = lean_array_get_size(x_52);
x_78 = lean_array_push(x_52, x_76);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_10, 0, x_79);
return x_10;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_54);
x_80 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__6;
x_81 = lean_string_append(x_66, x_80);
x_82 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__1;
x_83 = lean_string_append(x_81, x_82);
x_84 = 3;
x_85 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set_uint8(x_85, sizeof(void*)*1, x_84);
x_86 = lean_array_get_size(x_52);
x_87 = lean_array_push(x_52, x_85);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
lean_ctor_set(x_10, 0, x_88);
return x_10;
}
}
else
{
lean_object* x_89; 
lean_dec(x_54);
lean_dec(x_2);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_53);
lean_ctor_set(x_89, 1, x_52);
lean_ctor_set(x_10, 0, x_89);
return x_10;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_90 = lean_ctor_get(x_10, 1);
lean_inc(x_90);
lean_dec(x_10);
x_91 = lean_ctor_get(x_11, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_92 = x_11;
} else {
 lean_dec_ref(x_11);
 x_92 = lean_box(0);
}
x_93 = lean_ctor_get(x_12, 1);
lean_inc(x_93);
lean_dec(x_12);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
x_95 = l_Lake_instDataKindFilePath;
x_96 = lean_name_eq(x_94, x_95);
if (x_96 == 0)
{
uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_93);
x_97 = l_Lean_Name_isAnonymous(x_94);
x_98 = l_Lake_PartialBuildKey_toString(x_2);
x_99 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__1;
x_100 = lean_string_append(x_99, x_98);
lean_dec(x_98);
x_101 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__2;
x_102 = lean_string_append(x_100, x_101);
x_103 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__12___closed__1;
x_104 = lean_string_append(x_102, x_103);
x_105 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__4;
x_106 = lean_string_append(x_104, x_105);
if (x_97 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_107 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___spec__2___closed__1;
x_108 = l_Lean_Name_toString(x_94, x_9, x_107);
x_109 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__5;
x_110 = lean_string_append(x_109, x_108);
lean_dec(x_108);
x_111 = lean_string_append(x_110, x_109);
x_112 = lean_string_append(x_106, x_111);
lean_dec(x_111);
x_113 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__1;
x_114 = lean_string_append(x_112, x_113);
x_115 = 3;
x_116 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set_uint8(x_116, sizeof(void*)*1, x_115);
x_117 = lean_array_get_size(x_91);
x_118 = lean_array_push(x_91, x_116);
if (lean_is_scalar(x_92)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_92;
 lean_ctor_set_tag(x_119, 1);
}
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_90);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_94);
x_121 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__6;
x_122 = lean_string_append(x_106, x_121);
x_123 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__1;
x_124 = lean_string_append(x_122, x_123);
x_125 = 3;
x_126 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set_uint8(x_126, sizeof(void*)*1, x_125);
x_127 = lean_array_get_size(x_91);
x_128 = lean_array_push(x_91, x_126);
if (lean_is_scalar(x_92)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_92;
 lean_ctor_set_tag(x_129, 1);
}
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_90);
return x_130;
}
}
else
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_94);
lean_dec(x_2);
if (lean_is_scalar(x_92)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_92;
}
lean_ctor_set(x_131, 0, x_93);
lean_ctor_set(x_131, 1, x_91);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_90);
return x_132;
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_2);
x_133 = !lean_is_exclusive(x_10);
if (x_133 == 0)
{
lean_object* x_134; uint8_t x_135; 
x_134 = lean_ctor_get(x_10, 0);
lean_dec(x_134);
x_135 = !lean_is_exclusive(x_11);
if (x_135 == 0)
{
return x_10;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_11, 0);
x_137 = lean_ctor_get(x_11, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_11);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
lean_ctor_set(x_10, 0, x_138);
return x_10;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_139 = lean_ctor_get(x_10, 1);
lean_inc(x_139);
lean_dec(x_10);
x_140 = lean_ctor_get(x_11, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_11, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_142 = x_11;
} else {
 lean_dec_ref(x_11);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_141);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_139);
return x_144;
}
}
}
else
{
uint8_t x_145; 
lean_dec(x_2);
x_145 = !lean_is_exclusive(x_10);
if (x_145 == 0)
{
return x_10;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_10, 0);
x_147 = lean_ctor_get(x_10, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_10);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__13(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_3, x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_uget(x_2, x_3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_14 = l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__12(x_1, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_array_push(x_5, x_17);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_5 = x_19;
x_10 = x_18;
x_11 = x_16;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_14, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
return x_14;
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
lean_ctor_set(x_14, 0, x_28);
return x_14;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_dec(x_14);
x_30 = lean_ctor_get(x_15, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_32 = x_15;
} else {
 lean_dec_ref(x_15);
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
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_5);
lean_ctor_set(x_39, 1, x_10);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_11);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLib_recBuildShared___spec__14(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_array_uget(x_4, x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_4, x_3, x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_17 = l_Lake_ModuleFacet_fetch___rarg(x_14, x_1, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = 1;
x_23 = lean_usize_add(x_3, x_22);
x_24 = lean_array_uset(x_16, x_3, x_20);
x_3 = x_23;
x_4 = x_24;
x_9 = x_21;
x_10 = x_19;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_17, 0);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
return x_17;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_17, 0, x_31);
return x_17;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_dec(x_17);
x_33 = lean_ctor_get(x_18, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_18, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_35 = x_18;
} else {
 lean_dec_ref(x_18);
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
else
{
uint8_t x_38; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
return x_17;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_17, 0);
x_40 = lean_ctor_get(x_17, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_17);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__15(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_12 = lean_array_uget(x_1, x_2);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 8);
lean_inc(x_15);
lean_dec(x_14);
x_16 = 1;
x_17 = lean_box(x_16);
x_18 = lean_apply_1(x_15, x_17);
x_19 = lean_array_size(x_18);
x_20 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_21 = l_Array_mapMUnsafe_map___at_Lake_LeanLib_recBuildShared___spec__14(x_12, x_19, x_20, x_18, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = l_Array_append___rarg(x_4, x_24);
lean_dec(x_24);
x_27 = 1;
x_28 = lean_usize_add(x_2, x_27);
x_2 = x_28;
x_4 = x_26;
x_9 = x_25;
x_10 = x_23;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_21, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_22);
if (x_32 == 0)
{
return x_21;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_22, 0);
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_22);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_21, 0, x_35);
return x_21;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_21, 1);
lean_inc(x_36);
lean_dec(x_21);
x_37 = lean_ctor_get(x_22, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_22, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_39 = x_22;
} else {
 lean_dec_ref(x_22);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_42 = !lean_is_exclusive(x_21);
if (x_42 == 0)
{
return x_21;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_21, 0);
x_44 = lean_ctor_get(x_21, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_21);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_9);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_10);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lake_LeanLib_recBuildShared___spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_31; 
x_31 = lean_get_set_stdout(x_1, x_8);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = lean_ctor_get(x_35, 1);
x_40 = lean_get_set_stdout(x_32, x_36);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_35, 0, x_43);
x_9 = x_35;
x_10 = x_41;
goto block_30;
}
else
{
uint8_t x_44; 
lean_free_object(x_35);
lean_dec(x_39);
lean_dec(x_38);
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_40, 0);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_40);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_35, 0);
x_49 = lean_ctor_get(x_35, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_35);
x_50 = lean_get_set_stdout(x_32, x_36);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_49);
x_9 = x_54;
x_10 = x_51;
goto block_30;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_49);
lean_dec(x_48);
x_55 = lean_ctor_get(x_50, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_57 = x_50;
} else {
 lean_dec_ref(x_50);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_34, 1);
lean_inc(x_59);
lean_dec(x_34);
x_60 = !lean_is_exclusive(x_35);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_35, 0);
x_62 = lean_ctor_get(x_35, 1);
x_63 = lean_get_set_stdout(x_32, x_59);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_9 = x_35;
x_10 = x_64;
goto block_30;
}
else
{
uint8_t x_65; 
lean_free_object(x_35);
lean_dec(x_62);
lean_dec(x_61);
x_65 = !lean_is_exclusive(x_63);
if (x_65 == 0)
{
return x_63;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_63, 0);
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_63);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_35, 0);
x_70 = lean_ctor_get(x_35, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_35);
x_71 = lean_get_set_stdout(x_32, x_59);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_70);
x_9 = x_73;
x_10 = x_72;
goto block_30;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_70);
lean_dec(x_69);
x_74 = lean_ctor_get(x_71, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_76 = x_71;
} else {
 lean_dec_ref(x_71);
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
}
else
{
uint8_t x_78; 
lean_dec(x_32);
x_78 = !lean_is_exclusive(x_34);
if (x_78 == 0)
{
return x_34;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_34, 0);
x_80 = lean_ctor_get(x_34, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_34);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_82 = !lean_is_exclusive(x_31);
if (x_82 == 0)
{
return x_31;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_31, 0);
x_84 = lean_ctor_get(x_31, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_31);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
block_30:
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_14);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_19);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lake_LeanLib_recBuildShared___spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_31; 
x_31 = lean_get_set_stdin(x_1, x_8);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = lean_ctor_get(x_35, 1);
x_40 = lean_get_set_stdin(x_32, x_36);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_35, 0, x_43);
x_9 = x_35;
x_10 = x_41;
goto block_30;
}
else
{
uint8_t x_44; 
lean_free_object(x_35);
lean_dec(x_39);
lean_dec(x_38);
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_40, 0);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_40);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_35, 0);
x_49 = lean_ctor_get(x_35, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_35);
x_50 = lean_get_set_stdin(x_32, x_36);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_49);
x_9 = x_54;
x_10 = x_51;
goto block_30;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_49);
lean_dec(x_48);
x_55 = lean_ctor_get(x_50, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_57 = x_50;
} else {
 lean_dec_ref(x_50);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_34, 1);
lean_inc(x_59);
lean_dec(x_34);
x_60 = !lean_is_exclusive(x_35);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_35, 0);
x_62 = lean_ctor_get(x_35, 1);
x_63 = lean_get_set_stdin(x_32, x_59);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_9 = x_35;
x_10 = x_64;
goto block_30;
}
else
{
uint8_t x_65; 
lean_free_object(x_35);
lean_dec(x_62);
lean_dec(x_61);
x_65 = !lean_is_exclusive(x_63);
if (x_65 == 0)
{
return x_63;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_63, 0);
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_63);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_35, 0);
x_70 = lean_ctor_get(x_35, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_35);
x_71 = lean_get_set_stdin(x_32, x_59);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_70);
x_9 = x_73;
x_10 = x_72;
goto block_30;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_70);
lean_dec(x_69);
x_74 = lean_ctor_get(x_71, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_76 = x_71;
} else {
 lean_dec_ref(x_71);
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
}
else
{
uint8_t x_78; 
lean_dec(x_32);
x_78 = !lean_is_exclusive(x_34);
if (x_78 == 0)
{
return x_34;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_34, 0);
x_80 = lean_ctor_get(x_34, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_34);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_82 = !lean_is_exclusive(x_31);
if (x_82 == 0)
{
return x_31;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_31, 0);
x_84 = lean_ctor_get(x_31, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_31);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
block_30:
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_14);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_19);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lake_LeanLib_recBuildShared___spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_31; 
x_31 = lean_get_set_stderr(x_1, x_8);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = lean_ctor_get(x_35, 1);
x_40 = lean_get_set_stderr(x_32, x_36);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_35, 0, x_43);
x_9 = x_35;
x_10 = x_41;
goto block_30;
}
else
{
uint8_t x_44; 
lean_free_object(x_35);
lean_dec(x_39);
lean_dec(x_38);
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_40, 0);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_40);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_35, 0);
x_49 = lean_ctor_get(x_35, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_35);
x_50 = lean_get_set_stderr(x_32, x_36);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_49);
x_9 = x_54;
x_10 = x_51;
goto block_30;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_49);
lean_dec(x_48);
x_55 = lean_ctor_get(x_50, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_57 = x_50;
} else {
 lean_dec_ref(x_50);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_34, 1);
lean_inc(x_59);
lean_dec(x_34);
x_60 = !lean_is_exclusive(x_35);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_35, 0);
x_62 = lean_ctor_get(x_35, 1);
x_63 = lean_get_set_stderr(x_32, x_59);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_9 = x_35;
x_10 = x_64;
goto block_30;
}
else
{
uint8_t x_65; 
lean_free_object(x_35);
lean_dec(x_62);
lean_dec(x_61);
x_65 = !lean_is_exclusive(x_63);
if (x_65 == 0)
{
return x_63;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_63, 0);
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_63);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_35, 0);
x_70 = lean_ctor_get(x_35, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_35);
x_71 = lean_get_set_stderr(x_32, x_59);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_70);
x_9 = x_73;
x_10 = x_72;
goto block_30;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_70);
lean_dec(x_69);
x_74 = lean_ctor_get(x_71, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_76 = x_71;
} else {
 lean_dec_ref(x_71);
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
}
else
{
uint8_t x_78; 
lean_dec(x_32);
x_78 = !lean_is_exclusive(x_34);
if (x_78 == 0)
{
return x_34;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_34, 0);
x_80 = lean_ctor_get(x_34, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_34);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_82 = !lean_is_exclusive(x_31);
if (x_82 == 0)
{
return x_31;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_31, 0);
x_84 = lean_ctor_get(x_31, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_31);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
block_30:
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_14);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_19);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recBuildShared___spec__18(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__1;
x_10 = lean_st_mk_ref(x_9, x_8);
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
x_18 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_LeanLib_recBuildShared___spec__19), 8, 2);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_1);
x_19 = l_IO_withStdin___at_Lake_LeanLib_recBuildShared___spec__20(x_16, x_18, x_3, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_20, 1);
x_25 = lean_st_ref_get(x_14, x_21);
lean_dec(x_14);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_string_validate_utf8(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_28);
x_30 = l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__5;
x_31 = l_panic___at_String_fromUTF8_x21___spec__1(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_23);
lean_ctor_set(x_20, 0, x_32);
lean_ctor_set(x_25, 0, x_20);
return x_25;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_string_from_utf8_unchecked(x_28);
lean_dec(x_28);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_23);
lean_ctor_set(x_20, 0, x_34);
lean_ctor_set(x_25, 0, x_20);
return x_25;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_ctor_get(x_25, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_25);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_string_validate_utf8(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_37);
x_39 = l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__5;
x_40 = l_panic___at_String_fromUTF8_x21___spec__1(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_23);
lean_ctor_set(x_20, 0, x_41);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_20);
lean_ctor_set(x_42, 1, x_36);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_string_from_utf8_unchecked(x_37);
lean_dec(x_37);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_23);
lean_ctor_set(x_20, 0, x_44);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_20);
lean_ctor_set(x_45, 1, x_36);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_free_object(x_20);
lean_dec(x_24);
lean_dec(x_23);
x_46 = !lean_is_exclusive(x_25);
if (x_46 == 0)
{
return x_25;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_25, 0);
x_48 = lean_ctor_get(x_25, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_25);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_20, 0);
x_51 = lean_ctor_get(x_20, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_20);
x_52 = lean_st_ref_get(x_14, x_21);
lean_dec(x_14);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
x_56 = lean_ctor_get(x_53, 0);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_string_validate_utf8(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_56);
x_58 = l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__5;
x_59 = l_panic___at_String_fromUTF8_x21___spec__1(x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_50);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_51);
if (lean_is_scalar(x_55)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_55;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_54);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_string_from_utf8_unchecked(x_56);
lean_dec(x_56);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_50);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_51);
if (lean_is_scalar(x_55)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_55;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_54);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_51);
lean_dec(x_50);
x_67 = lean_ctor_get(x_52, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_52, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_69 = x_52;
} else {
 lean_dec_ref(x_52);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_14);
x_71 = !lean_is_exclusive(x_19);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_19, 0);
lean_dec(x_72);
x_73 = !lean_is_exclusive(x_20);
if (x_73 == 0)
{
return x_19;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_20, 0);
x_75 = lean_ctor_get(x_20, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_20);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set(x_19, 0, x_76);
return x_19;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_19, 1);
lean_inc(x_77);
lean_dec(x_19);
x_78 = lean_ctor_get(x_20, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_20, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_80 = x_20;
} else {
 lean_dec_ref(x_20);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_77);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_14);
x_83 = !lean_is_exclusive(x_19);
if (x_83 == 0)
{
return x_19;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_19, 0);
x_85 = lean_ctor_get(x_19, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_19);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_inc(x_17);
x_87 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lake_LeanLib_recBuildShared___spec__21), 8, 2);
lean_closure_set(x_87, 0, x_17);
lean_closure_set(x_87, 1, x_1);
x_88 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lake_LeanLib_recBuildShared___spec__19), 8, 2);
lean_closure_set(x_88, 0, x_17);
lean_closure_set(x_88, 1, x_87);
x_89 = l_IO_withStdin___at_Lake_LeanLib_recBuildShared___spec__20(x_16, x_88, x_3, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = !lean_is_exclusive(x_90);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_90, 0);
x_94 = lean_ctor_get(x_90, 1);
x_95 = lean_st_ref_get(x_14, x_91);
lean_dec(x_14);
if (lean_obj_tag(x_95) == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_97 = lean_ctor_get(x_95, 0);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec(x_97);
x_99 = lean_string_validate_utf8(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_98);
x_100 = l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__5;
x_101 = l_panic___at_String_fromUTF8_x21___spec__1(x_100);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_93);
lean_ctor_set(x_90, 0, x_102);
lean_ctor_set(x_95, 0, x_90);
return x_95;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_string_from_utf8_unchecked(x_98);
lean_dec(x_98);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_93);
lean_ctor_set(x_90, 0, x_104);
lean_ctor_set(x_95, 0, x_90);
return x_95;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_105 = lean_ctor_get(x_95, 0);
x_106 = lean_ctor_get(x_95, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_95);
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_string_validate_utf8(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_107);
x_109 = l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__5;
x_110 = l_panic___at_String_fromUTF8_x21___spec__1(x_109);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_93);
lean_ctor_set(x_90, 0, x_111);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_90);
lean_ctor_set(x_112, 1, x_106);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_string_from_utf8_unchecked(x_107);
lean_dec(x_107);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_93);
lean_ctor_set(x_90, 0, x_114);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_90);
lean_ctor_set(x_115, 1, x_106);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_free_object(x_90);
lean_dec(x_94);
lean_dec(x_93);
x_116 = !lean_is_exclusive(x_95);
if (x_116 == 0)
{
return x_95;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_95, 0);
x_118 = lean_ctor_get(x_95, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_95);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_90, 0);
x_121 = lean_ctor_get(x_90, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_90);
x_122 = lean_st_ref_get(x_14, x_91);
lean_dec(x_14);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
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
x_126 = lean_ctor_get(x_123, 0);
lean_inc(x_126);
lean_dec(x_123);
x_127 = lean_string_validate_utf8(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_126);
x_128 = l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__5;
x_129 = l_panic___at_String_fromUTF8_x21___spec__1(x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_120);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_121);
if (lean_is_scalar(x_125)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_125;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_124);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_133 = lean_string_from_utf8_unchecked(x_126);
lean_dec(x_126);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_120);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_121);
if (lean_is_scalar(x_125)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_125;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_124);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_121);
lean_dec(x_120);
x_137 = lean_ctor_get(x_122, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_122, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_139 = x_122;
} else {
 lean_dec_ref(x_122);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
}
else
{
uint8_t x_141; 
lean_dec(x_14);
x_141 = !lean_is_exclusive(x_89);
if (x_141 == 0)
{
lean_object* x_142; uint8_t x_143; 
x_142 = lean_ctor_get(x_89, 0);
lean_dec(x_142);
x_143 = !lean_is_exclusive(x_90);
if (x_143 == 0)
{
return x_89;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_90, 0);
x_145 = lean_ctor_get(x_90, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_90);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
lean_ctor_set(x_89, 0, x_146);
return x_89;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_147 = lean_ctor_get(x_89, 1);
lean_inc(x_147);
lean_dec(x_89);
x_148 = lean_ctor_get(x_90, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_90, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_150 = x_90;
} else {
 lean_dec_ref(x_90);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_149);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_147);
return x_152;
}
}
}
else
{
uint8_t x_153; 
lean_dec(x_14);
x_153 = !lean_is_exclusive(x_89);
if (x_153 == 0)
{
return x_89;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_89, 0);
x_155 = lean_ctor_get(x_89, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_89);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_157 = !lean_is_exclusive(x_13);
if (x_157 == 0)
{
return x_13;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_13, 0);
x_159 = lean_ctor_get(x_13, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_13);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
else
{
uint8_t x_161; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_161 = !lean_is_exclusive(x_10);
if (x_161 == 0)
{
return x_10;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_10, 0);
x_163 = lean_ctor_get(x_10, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_10);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at_Lake_LeanLib_recBuildShared___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_91; lean_object* x_92; 
x_8 = lean_array_get_size(x_6);
x_91 = 1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_92 = l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recBuildShared___spec__18(x_1, x_91, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec(x_93);
x_97 = lean_ctor_get(x_94, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_94, 1);
lean_inc(x_98);
lean_dec(x_94);
x_99 = lean_string_utf8_byte_size(x_97);
x_100 = lean_unsigned_to_nat(0u);
x_101 = lean_nat_dec_eq(x_99, x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_102 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_97, x_99, x_100);
x_103 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_97, x_102, x_99);
x_104 = lean_string_utf8_extract(x_97, x_102, x_103);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_97);
x_105 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__2;
x_106 = lean_string_append(x_105, x_104);
lean_dec(x_104);
x_107 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__1;
x_108 = lean_string_append(x_106, x_107);
x_109 = 1;
x_110 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set_uint8(x_110, sizeof(void*)*1, x_109);
x_111 = lean_array_push(x_96, x_110);
x_112 = lean_box(0);
x_113 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___lambda__1(x_98, x_112, x_2, x_3, x_4, x_5, x_111, x_95);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_9 = x_114;
x_10 = x_115;
goto block_90;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_99);
lean_dec(x_97);
x_116 = lean_box(0);
x_117 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___lambda__1(x_98, x_116, x_2, x_3, x_4, x_5, x_96, x_95);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_9 = x_118;
x_10 = x_119;
goto block_90;
}
}
else
{
lean_object* x_120; uint8_t x_121; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_120 = lean_ctor_get(x_92, 1);
lean_inc(x_120);
lean_dec(x_92);
x_121 = !lean_is_exclusive(x_93);
if (x_121 == 0)
{
x_9 = x_93;
x_10 = x_120;
goto block_90;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_93, 0);
x_123 = lean_ctor_get(x_93, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_93);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_9 = x_124;
x_10 = x_120;
goto block_90;
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_125 = !lean_is_exclusive(x_92);
if (x_125 == 0)
{
return x_92;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_92, 0);
x_127 = lean_ctor_get(x_92, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_92);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
block_90:
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 1);
x_14 = lean_array_get_size(x_13);
x_15 = lean_nat_dec_lt(x_8, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec(x_8);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_inc(x_13);
x_17 = l_Array_shrink___rarg(x_13, x_8);
x_18 = l_Array_extract___rarg(x_13, x_8, x_14);
lean_dec(x_14);
lean_dec(x_13);
x_19 = lean_alloc_closure((void*)(l_Lake_JobResult_prependLog___rarg), 2, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_dec(x_22);
x_23 = l_Task_Priority_default;
x_24 = 1;
x_25 = lean_task_map(x_19, x_21, x_23, x_24);
x_26 = l_Lake_instDataKindDynlib;
lean_ctor_set(x_12, 1, x_26);
lean_ctor_set(x_12, 0, x_25);
lean_ctor_set(x_9, 1, x_17);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_9);
lean_ctor_set(x_27, 1, x_10);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_12, 0);
x_29 = lean_ctor_get(x_12, 2);
x_30 = lean_ctor_get_uint8(x_12, sizeof(void*)*3);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_12);
x_31 = l_Task_Priority_default;
x_32 = 1;
x_33 = lean_task_map(x_19, x_28, x_31, x_32);
x_34 = l_Lake_instDataKindDynlib;
x_35 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_29);
lean_ctor_set_uint8(x_35, sizeof(void*)*3, x_30);
lean_ctor_set(x_9, 1, x_17);
lean_ctor_set(x_9, 0, x_35);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_9);
lean_ctor_set(x_36, 1, x_10);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_9, 0);
x_38 = lean_ctor_get(x_9, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_9);
x_39 = lean_array_get_size(x_38);
x_40 = lean_nat_dec_lt(x_8, x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_39);
lean_dec(x_8);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_10);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_inc(x_38);
x_43 = l_Array_shrink___rarg(x_38, x_8);
x_44 = l_Array_extract___rarg(x_38, x_8, x_39);
lean_dec(x_39);
lean_dec(x_38);
x_45 = lean_alloc_closure((void*)(l_Lake_JobResult_prependLog___rarg), 2, 1);
lean_closure_set(x_45, 0, x_44);
x_46 = lean_ctor_get(x_37, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_37, 2);
lean_inc(x_47);
x_48 = lean_ctor_get_uint8(x_37, sizeof(void*)*3);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 x_49 = x_37;
} else {
 lean_dec_ref(x_37);
 x_49 = lean_box(0);
}
x_50 = l_Task_Priority_default;
x_51 = 1;
x_52 = lean_task_map(x_45, x_46, x_50, x_51);
x_53 = l_Lake_instDataKindDynlib;
if (lean_is_scalar(x_49)) {
 x_54 = lean_alloc_ctor(0, 3, 1);
} else {
 x_54 = x_49;
}
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_47);
lean_ctor_set_uint8(x_54, sizeof(void*)*3, x_48);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_43);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_10);
return x_56;
}
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_9);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_58 = lean_ctor_get(x_9, 1);
x_59 = lean_ctor_get(x_9, 0);
lean_dec(x_59);
lean_inc(x_58);
x_60 = l_Array_shrink___rarg(x_58, x_8);
x_61 = lean_array_get_size(x_58);
x_62 = l_Array_extract___rarg(x_58, x_8, x_61);
lean_dec(x_61);
lean_dec(x_58);
x_63 = 0;
x_64 = l_Lake_BuildTrace_nil;
x_65 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*2, x_63);
x_66 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_9, 1, x_65);
lean_ctor_set(x_9, 0, x_66);
x_67 = lean_task_pure(x_9);
x_68 = l_Lake_instDataKindDynlib;
x_69 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__1;
x_70 = 0;
x_71 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_68);
lean_ctor_set(x_71, 2, x_69);
lean_ctor_set_uint8(x_71, sizeof(void*)*3, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_60);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_10);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_74 = lean_ctor_get(x_9, 1);
lean_inc(x_74);
lean_dec(x_9);
lean_inc(x_74);
x_75 = l_Array_shrink___rarg(x_74, x_8);
x_76 = lean_array_get_size(x_74);
x_77 = l_Array_extract___rarg(x_74, x_8, x_76);
lean_dec(x_76);
lean_dec(x_74);
x_78 = 0;
x_79 = l_Lake_BuildTrace_nil;
x_80 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set_uint8(x_80, sizeof(void*)*2, x_78);
x_81 = lean_unsigned_to_nat(0u);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
x_83 = lean_task_pure(x_82);
x_84 = l_Lake_instDataKindDynlib;
x_85 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__1;
x_86 = 0;
x_87 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_87, 0, x_83);
lean_ctor_set(x_87, 1, x_84);
lean_ctor_set(x_87, 2, x_85);
lean_ctor_set_uint8(x_87, sizeof(void*)*3, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_75);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_10);
return x_89;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___at_Lake_LeanLib_recBuildShared___spec__16(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_7);
x_10 = l_Lake_ensureJob___at_Lake_LeanLib_recBuildShared___spec__17(x_2, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_17 = lean_ctor_get(x_12, 2);
lean_dec(x_17);
lean_ctor_set(x_12, 2, x_1);
lean_ctor_set_uint8(x_12, sizeof(void*)*3, x_3);
x_18 = lean_ctor_get(x_7, 3);
lean_inc(x_18);
lean_dec(x_7);
x_19 = lean_st_ref_take(x_18, x_13);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_12);
x_22 = l_Lake_Job_toOpaque___rarg(x_12);
x_23 = lean_array_push(x_20, x_22);
x_24 = lean_st_ref_set(x_18, x_23, x_21);
lean_dec(x_18);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = l_Lake_Job_renew___rarg(x_12);
lean_ctor_set(x_11, 0, x_27);
lean_ctor_set(x_24, 0, x_11);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = l_Lake_Job_renew___rarg(x_12);
lean_ctor_set(x_11, 0, x_29);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_11);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_31 = lean_ctor_get(x_12, 0);
x_32 = lean_ctor_get(x_12, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_12);
x_33 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_1);
lean_ctor_set_uint8(x_33, sizeof(void*)*3, x_3);
x_34 = lean_ctor_get(x_7, 3);
lean_inc(x_34);
lean_dec(x_7);
x_35 = lean_st_ref_take(x_34, x_13);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_33);
x_38 = l_Lake_Job_toOpaque___rarg(x_33);
x_39 = lean_array_push(x_36, x_38);
x_40 = lean_st_ref_set(x_34, x_39, x_37);
lean_dec(x_34);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
x_43 = l_Lake_Job_renew___rarg(x_33);
lean_ctor_set(x_11, 0, x_43);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_11);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_45 = lean_ctor_get(x_11, 1);
lean_inc(x_45);
lean_dec(x_11);
x_46 = lean_ctor_get(x_12, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_12, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 x_48 = x_12;
} else {
 lean_dec_ref(x_12);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(0, 3, 1);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_49, 2, x_1);
lean_ctor_set_uint8(x_49, sizeof(void*)*3, x_3);
x_50 = lean_ctor_get(x_7, 3);
lean_inc(x_50);
lean_dec(x_7);
x_51 = lean_st_ref_take(x_50, x_13);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_49);
x_54 = l_Lake_Job_toOpaque___rarg(x_49);
x_55 = lean_array_push(x_52, x_54);
x_56 = lean_st_ref_set(x_50, x_55, x_53);
lean_dec(x_50);
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
x_59 = l_Lake_Job_renew___rarg(x_49);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_45);
if (lean_is_scalar(x_58)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_58;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_57);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec(x_7);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_10);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_10, 0);
lean_dec(x_63);
x_64 = !lean_is_exclusive(x_11);
if (x_64 == 0)
{
return x_10;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_11, 0);
x_66 = lean_ctor_get(x_11, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_11);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_10, 0, x_67);
return x_10;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_10, 1);
lean_inc(x_68);
lean_dec(x_10);
x_69 = lean_ctor_get(x_11, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_11, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_71 = x_11;
} else {
 lean_dec_ref(x_11);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_68);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_7);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_10);
if (x_74 == 0)
{
return x_10;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_10, 0);
x_76 = lean_ctor_get(x_10, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_10);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildShared___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_1064; lean_object* x_1065; lean_object* x_1081; lean_object* x_1082; lean_object* x_1106; lean_object* x_1107; 
x_1106 = lean_ctor_get(x_7, 0);
lean_inc(x_1106);
lean_dec(x_7);
x_1107 = lean_io_wait(x_1106, x_13);
if (lean_obj_tag(x_1107) == 0)
{
lean_object* x_1108; 
x_1108 = lean_ctor_get(x_1107, 0);
lean_inc(x_1108);
if (lean_obj_tag(x_1108) == 0)
{
lean_object* x_1109; lean_object* x_1110; uint8_t x_1111; 
x_1109 = lean_ctor_get(x_1108, 1);
lean_inc(x_1109);
x_1110 = lean_ctor_get(x_1107, 1);
lean_inc(x_1110);
lean_dec(x_1107);
x_1111 = !lean_is_exclusive(x_1108);
if (x_1111 == 0)
{
lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; uint8_t x_1117; 
x_1112 = lean_ctor_get(x_1108, 0);
x_1113 = lean_ctor_get(x_1108, 1);
lean_dec(x_1113);
x_1114 = lean_ctor_get(x_1109, 0);
lean_inc(x_1114);
lean_dec(x_1109);
x_1115 = lean_array_get_size(x_1114);
x_1116 = lean_unsigned_to_nat(0u);
x_1117 = lean_nat_dec_lt(x_1116, x_1115);
if (x_1117 == 0)
{
lean_dec(x_1115);
lean_dec(x_1114);
lean_ctor_set(x_1108, 1, x_12);
x_1081 = x_1108;
x_1082 = x_1110;
goto block_1105;
}
else
{
uint8_t x_1118; 
x_1118 = lean_nat_dec_le(x_1115, x_1115);
if (x_1118 == 0)
{
lean_dec(x_1115);
lean_dec(x_1114);
lean_ctor_set(x_1108, 1, x_12);
x_1081 = x_1108;
x_1082 = x_1110;
goto block_1105;
}
else
{
size_t x_1119; size_t x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; uint8_t x_1125; 
lean_free_object(x_1108);
x_1119 = 0;
x_1120 = lean_usize_of_nat(x_1115);
lean_dec(x_1115);
x_1121 = lean_box(0);
x_1122 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_1114, x_1119, x_1120, x_1121, x_12, x_1110);
lean_dec(x_1114);
x_1123 = lean_ctor_get(x_1122, 0);
lean_inc(x_1123);
x_1124 = lean_ctor_get(x_1122, 1);
lean_inc(x_1124);
lean_dec(x_1122);
x_1125 = !lean_is_exclusive(x_1123);
if (x_1125 == 0)
{
lean_object* x_1126; 
x_1126 = lean_ctor_get(x_1123, 0);
lean_dec(x_1126);
lean_ctor_set(x_1123, 0, x_1112);
x_1081 = x_1123;
x_1082 = x_1124;
goto block_1105;
}
else
{
lean_object* x_1127; lean_object* x_1128; 
x_1127 = lean_ctor_get(x_1123, 1);
lean_inc(x_1127);
lean_dec(x_1123);
x_1128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1128, 0, x_1112);
lean_ctor_set(x_1128, 1, x_1127);
x_1081 = x_1128;
x_1082 = x_1124;
goto block_1105;
}
}
}
}
else
{
lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; uint8_t x_1133; 
x_1129 = lean_ctor_get(x_1108, 0);
lean_inc(x_1129);
lean_dec(x_1108);
x_1130 = lean_ctor_get(x_1109, 0);
lean_inc(x_1130);
lean_dec(x_1109);
x_1131 = lean_array_get_size(x_1130);
x_1132 = lean_unsigned_to_nat(0u);
x_1133 = lean_nat_dec_lt(x_1132, x_1131);
if (x_1133 == 0)
{
lean_object* x_1134; 
lean_dec(x_1131);
lean_dec(x_1130);
x_1134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1134, 0, x_1129);
lean_ctor_set(x_1134, 1, x_12);
x_1081 = x_1134;
x_1082 = x_1110;
goto block_1105;
}
else
{
uint8_t x_1135; 
x_1135 = lean_nat_dec_le(x_1131, x_1131);
if (x_1135 == 0)
{
lean_object* x_1136; 
lean_dec(x_1131);
lean_dec(x_1130);
x_1136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1136, 0, x_1129);
lean_ctor_set(x_1136, 1, x_12);
x_1081 = x_1136;
x_1082 = x_1110;
goto block_1105;
}
else
{
size_t x_1137; size_t x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; 
x_1137 = 0;
x_1138 = lean_usize_of_nat(x_1131);
lean_dec(x_1131);
x_1139 = lean_box(0);
x_1140 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_1130, x_1137, x_1138, x_1139, x_12, x_1110);
lean_dec(x_1130);
x_1141 = lean_ctor_get(x_1140, 0);
lean_inc(x_1141);
x_1142 = lean_ctor_get(x_1140, 1);
lean_inc(x_1142);
lean_dec(x_1140);
x_1143 = lean_ctor_get(x_1141, 1);
lean_inc(x_1143);
if (lean_is_exclusive(x_1141)) {
 lean_ctor_release(x_1141, 0);
 lean_ctor_release(x_1141, 1);
 x_1144 = x_1141;
} else {
 lean_dec_ref(x_1141);
 x_1144 = lean_box(0);
}
if (lean_is_scalar(x_1144)) {
 x_1145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1145 = x_1144;
}
lean_ctor_set(x_1145, 0, x_1129);
lean_ctor_set(x_1145, 1, x_1143);
x_1081 = x_1145;
x_1082 = x_1142;
goto block_1105;
}
}
}
}
else
{
lean_object* x_1146; lean_object* x_1147; uint8_t x_1148; 
x_1146 = lean_ctor_get(x_1108, 1);
lean_inc(x_1146);
x_1147 = lean_ctor_get(x_1107, 1);
lean_inc(x_1147);
lean_dec(x_1107);
x_1148 = !lean_is_exclusive(x_1108);
if (x_1148 == 0)
{
lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; uint8_t x_1154; 
x_1149 = lean_ctor_get(x_1108, 0);
x_1150 = lean_ctor_get(x_1108, 1);
lean_dec(x_1150);
x_1151 = lean_ctor_get(x_1146, 0);
lean_inc(x_1151);
lean_dec(x_1146);
x_1152 = lean_array_get_size(x_1151);
x_1153 = lean_unsigned_to_nat(0u);
x_1154 = lean_nat_dec_lt(x_1153, x_1152);
if (x_1154 == 0)
{
lean_dec(x_1152);
lean_dec(x_1151);
lean_ctor_set(x_1108, 1, x_12);
x_1081 = x_1108;
x_1082 = x_1147;
goto block_1105;
}
else
{
uint8_t x_1155; 
x_1155 = lean_nat_dec_le(x_1152, x_1152);
if (x_1155 == 0)
{
lean_dec(x_1152);
lean_dec(x_1151);
lean_ctor_set(x_1108, 1, x_12);
x_1081 = x_1108;
x_1082 = x_1147;
goto block_1105;
}
else
{
size_t x_1156; size_t x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; uint8_t x_1162; 
lean_free_object(x_1108);
x_1156 = 0;
x_1157 = lean_usize_of_nat(x_1152);
lean_dec(x_1152);
x_1158 = lean_box(0);
x_1159 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_1151, x_1156, x_1157, x_1158, x_12, x_1147);
lean_dec(x_1151);
x_1160 = lean_ctor_get(x_1159, 0);
lean_inc(x_1160);
x_1161 = lean_ctor_get(x_1159, 1);
lean_inc(x_1161);
lean_dec(x_1159);
x_1162 = !lean_is_exclusive(x_1160);
if (x_1162 == 0)
{
lean_object* x_1163; 
x_1163 = lean_ctor_get(x_1160, 0);
lean_dec(x_1163);
lean_ctor_set_tag(x_1160, 1);
lean_ctor_set(x_1160, 0, x_1149);
x_1081 = x_1160;
x_1082 = x_1161;
goto block_1105;
}
else
{
lean_object* x_1164; lean_object* x_1165; 
x_1164 = lean_ctor_get(x_1160, 1);
lean_inc(x_1164);
lean_dec(x_1160);
x_1165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1165, 0, x_1149);
lean_ctor_set(x_1165, 1, x_1164);
x_1081 = x_1165;
x_1082 = x_1161;
goto block_1105;
}
}
}
}
else
{
lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; uint8_t x_1170; 
x_1166 = lean_ctor_get(x_1108, 0);
lean_inc(x_1166);
lean_dec(x_1108);
x_1167 = lean_ctor_get(x_1146, 0);
lean_inc(x_1167);
lean_dec(x_1146);
x_1168 = lean_array_get_size(x_1167);
x_1169 = lean_unsigned_to_nat(0u);
x_1170 = lean_nat_dec_lt(x_1169, x_1168);
if (x_1170 == 0)
{
lean_object* x_1171; 
lean_dec(x_1168);
lean_dec(x_1167);
x_1171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1171, 0, x_1166);
lean_ctor_set(x_1171, 1, x_12);
x_1081 = x_1171;
x_1082 = x_1147;
goto block_1105;
}
else
{
uint8_t x_1172; 
x_1172 = lean_nat_dec_le(x_1168, x_1168);
if (x_1172 == 0)
{
lean_object* x_1173; 
lean_dec(x_1168);
lean_dec(x_1167);
x_1173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1173, 0, x_1166);
lean_ctor_set(x_1173, 1, x_12);
x_1081 = x_1173;
x_1082 = x_1147;
goto block_1105;
}
else
{
size_t x_1174; size_t x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; 
x_1174 = 0;
x_1175 = lean_usize_of_nat(x_1168);
lean_dec(x_1168);
x_1176 = lean_box(0);
x_1177 = l_Array_foldlMUnsafe_fold___at_Lake_Job_await___spec__1(x_1167, x_1174, x_1175, x_1176, x_12, x_1147);
lean_dec(x_1167);
x_1178 = lean_ctor_get(x_1177, 0);
lean_inc(x_1178);
x_1179 = lean_ctor_get(x_1177, 1);
lean_inc(x_1179);
lean_dec(x_1177);
x_1180 = lean_ctor_get(x_1178, 1);
lean_inc(x_1180);
if (lean_is_exclusive(x_1178)) {
 lean_ctor_release(x_1178, 0);
 lean_ctor_release(x_1178, 1);
 x_1181 = x_1178;
} else {
 lean_dec_ref(x_1178);
 x_1181 = lean_box(0);
}
if (lean_is_scalar(x_1181)) {
 x_1182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1182 = x_1181;
 lean_ctor_set_tag(x_1182, 1);
}
lean_ctor_set(x_1182, 0, x_1166);
lean_ctor_set(x_1182, 1, x_1180);
x_1081 = x_1182;
x_1082 = x_1179;
goto block_1105;
}
}
}
}
}
else
{
uint8_t x_1183; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_1183 = !lean_is_exclusive(x_1107);
if (x_1183 == 0)
{
return x_1107;
}
else
{
lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; 
x_1184 = lean_ctor_get(x_1107, 0);
x_1185 = lean_ctor_get(x_1107, 1);
lean_inc(x_1185);
lean_inc(x_1184);
lean_dec(x_1107);
x_1186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1186, 0, x_1184);
lean_ctor_set(x_1186, 1, x_1185);
return x_1186;
}
}
block_1063:
{
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_659; lean_object* x_660; lean_object* x_713; lean_object* x_714; uint8_t x_715; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
x_713 = lean_array_get_size(x_17);
x_714 = lean_unsigned_to_nat(0u);
x_715 = lean_nat_dec_lt(x_714, x_713);
if (x_715 == 0)
{
lean_object* x_716; 
lean_dec(x_713);
x_716 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2;
lean_ctor_set(x_14, 0, x_716);
x_659 = x_14;
x_660 = x_15;
goto block_712;
}
else
{
uint8_t x_717; 
x_717 = lean_nat_dec_le(x_713, x_713);
if (x_717 == 0)
{
lean_object* x_718; 
lean_dec(x_713);
x_718 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2;
lean_ctor_set(x_14, 0, x_718);
x_659 = x_14;
x_660 = x_15;
goto block_712;
}
else
{
size_t x_719; size_t x_720; lean_object* x_721; lean_object* x_722; 
lean_free_object(x_14);
x_719 = 0;
x_720 = lean_usize_of_nat(x_713);
lean_dec(x_713);
x_721 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_722 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__15(x_17, x_719, x_720, x_721, x_8, x_9, x_10, x_11, x_18, x_15);
if (lean_obj_tag(x_722) == 0)
{
lean_object* x_723; lean_object* x_724; 
x_723 = lean_ctor_get(x_722, 0);
lean_inc(x_723);
x_724 = lean_ctor_get(x_722, 1);
lean_inc(x_724);
lean_dec(x_722);
x_659 = x_723;
x_660 = x_724;
goto block_712;
}
else
{
uint8_t x_725; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_725 = !lean_is_exclusive(x_722);
if (x_725 == 0)
{
return x_722;
}
else
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; 
x_726 = lean_ctor_get(x_722, 0);
x_727 = lean_ctor_get(x_722, 1);
lean_inc(x_727);
lean_inc(x_726);
lean_dec(x_722);
x_728 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_728, 0, x_726);
lean_ctor_set(x_728, 1, x_727);
return x_728;
}
}
}
}
block_658:
{
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_115; lean_object* x_116; lean_object* x_315; lean_object* x_316; lean_object* x_369; lean_object* x_370; uint8_t x_371; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 1);
x_369 = lean_array_get_size(x_17);
x_370 = lean_unsigned_to_nat(0u);
x_371 = lean_nat_dec_lt(x_370, x_369);
if (x_371 == 0)
{
lean_object* x_372; 
lean_dec(x_369);
lean_dec(x_17);
x_372 = l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
lean_ctor_set(x_19, 0, x_372);
x_315 = x_19;
x_316 = x_20;
goto block_368;
}
else
{
uint8_t x_373; 
x_373 = lean_nat_dec_le(x_369, x_369);
if (x_373 == 0)
{
lean_object* x_374; 
lean_dec(x_369);
lean_dec(x_17);
x_374 = l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
lean_ctor_set(x_19, 0, x_374);
x_315 = x_19;
x_316 = x_20;
goto block_368;
}
else
{
size_t x_375; size_t x_376; lean_object* x_377; lean_object* x_378; 
lean_free_object(x_19);
x_375 = 0;
x_376 = lean_usize_of_nat(x_369);
lean_dec(x_369);
x_377 = l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_378 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__11(x_17, x_375, x_376, x_377, x_8, x_9, x_10, x_11, x_23, x_20);
lean_dec(x_17);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; lean_object* x_380; 
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
lean_dec(x_378);
x_315 = x_379;
x_316 = x_380;
goto block_368;
}
else
{
uint8_t x_381; 
lean_dec(x_6);
lean_dec(x_5);
x_381 = !lean_is_exclusive(x_378);
if (x_381 == 0)
{
x_24 = x_378;
goto block_114;
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_382 = lean_ctor_get(x_378, 0);
x_383 = lean_ctor_get(x_378, 1);
lean_inc(x_383);
lean_inc(x_382);
lean_dec(x_378);
x_384 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_384, 0, x_382);
lean_ctor_set(x_384, 1, x_383);
x_24 = x_384;
goto block_114;
}
}
}
}
block_114:
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; 
x_28 = lean_ctor_get(x_25, 0);
x_29 = lean_ctor_get(x_25, 1);
x_30 = lean_ctor_get(x_1, 4);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_2, 3);
lean_inc(x_32);
lean_dec(x_2);
x_33 = lean_ctor_get(x_32, 6);
lean_inc(x_33);
x_34 = l_Lake_joinRelative(x_31, x_33);
lean_dec(x_33);
x_35 = lean_ctor_get(x_32, 8);
lean_inc(x_35);
x_36 = l_Lake_joinRelative(x_34, x_35);
lean_dec(x_35);
x_37 = l_Lake_nameToSharedLib(x_30);
x_38 = l_Lake_joinRelative(x_36, x_37);
lean_dec(x_37);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_dec(x_32);
x_40 = lean_ctor_get(x_39, 9);
lean_inc(x_40);
x_41 = lean_ctor_get(x_1, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 9);
lean_inc(x_42);
x_43 = l_Array_append___rarg(x_40, x_42);
lean_dec(x_42);
x_44 = lean_ctor_get(x_39, 8);
lean_inc(x_44);
lean_dec(x_39);
x_45 = lean_ctor_get(x_41, 8);
lean_inc(x_45);
lean_dec(x_41);
x_46 = l_Array_append___rarg(x_44, x_45);
lean_dec(x_45);
x_47 = lean_ctor_get(x_1, 2);
lean_inc(x_47);
lean_dec(x_1);
x_48 = lean_array_get_size(x_47);
lean_dec(x_47);
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_nat_dec_eq(x_48, x_49);
lean_dec(x_48);
x_51 = l_System_Platform_isWindows;
x_52 = l_Lake_BuildTrace_nil;
x_53 = l_Lake_buildLeanSharedLib(x_30, x_38, x_22, x_28, x_43, x_46, x_50, x_51, x_8, x_9, x_10, x_11, x_52, x_26);
lean_dec(x_22);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_ctor_set(x_25, 0, x_55);
lean_ctor_set(x_53, 0, x_25);
return x_53;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_53, 0);
x_57 = lean_ctor_get(x_53, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_53);
lean_ctor_set(x_25, 0, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_25);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_free_object(x_25);
lean_dec(x_29);
x_59 = !lean_is_exclusive(x_53);
if (x_59 == 0)
{
return x_53;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_53, 0);
x_61 = lean_ctor_get(x_53, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_53);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; 
x_63 = lean_ctor_get(x_25, 0);
x_64 = lean_ctor_get(x_25, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_25);
x_65 = lean_ctor_get(x_1, 4);
lean_inc(x_65);
x_66 = lean_ctor_get(x_2, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_2, 3);
lean_inc(x_67);
lean_dec(x_2);
x_68 = lean_ctor_get(x_67, 6);
lean_inc(x_68);
x_69 = l_Lake_joinRelative(x_66, x_68);
lean_dec(x_68);
x_70 = lean_ctor_get(x_67, 8);
lean_inc(x_70);
x_71 = l_Lake_joinRelative(x_69, x_70);
lean_dec(x_70);
x_72 = l_Lake_nameToSharedLib(x_65);
x_73 = l_Lake_joinRelative(x_71, x_72);
lean_dec(x_72);
x_74 = lean_ctor_get(x_67, 1);
lean_inc(x_74);
lean_dec(x_67);
x_75 = lean_ctor_get(x_74, 9);
lean_inc(x_75);
x_76 = lean_ctor_get(x_1, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_76, 9);
lean_inc(x_77);
x_78 = l_Array_append___rarg(x_75, x_77);
lean_dec(x_77);
x_79 = lean_ctor_get(x_74, 8);
lean_inc(x_79);
lean_dec(x_74);
x_80 = lean_ctor_get(x_76, 8);
lean_inc(x_80);
lean_dec(x_76);
x_81 = l_Array_append___rarg(x_79, x_80);
lean_dec(x_80);
x_82 = lean_ctor_get(x_1, 2);
lean_inc(x_82);
lean_dec(x_1);
x_83 = lean_array_get_size(x_82);
lean_dec(x_82);
x_84 = lean_unsigned_to_nat(1u);
x_85 = lean_nat_dec_eq(x_83, x_84);
lean_dec(x_83);
x_86 = l_System_Platform_isWindows;
x_87 = l_Lake_BuildTrace_nil;
x_88 = l_Lake_buildLeanSharedLib(x_65, x_73, x_22, x_63, x_78, x_81, x_85, x_86, x_8, x_9, x_10, x_11, x_87, x_26);
lean_dec(x_22);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
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
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_64);
if (lean_is_scalar(x_91)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_91;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_90);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_64);
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
uint8_t x_98; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_24);
if (x_98 == 0)
{
lean_object* x_99; uint8_t x_100; 
x_99 = lean_ctor_get(x_24, 0);
lean_dec(x_99);
x_100 = !lean_is_exclusive(x_25);
if (x_100 == 0)
{
return x_24;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_25, 0);
x_102 = lean_ctor_get(x_25, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_25);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set(x_24, 0, x_103);
return x_24;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_104 = lean_ctor_get(x_24, 1);
lean_inc(x_104);
lean_dec(x_24);
x_105 = lean_ctor_get(x_25, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_25, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_107 = x_25;
} else {
 lean_dec_ref(x_25);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_104);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_24);
if (x_110 == 0)
{
return x_24;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_24, 0);
x_112 = lean_ctor_get(x_24, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_24);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
block_314:
{
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_117 = lean_ctor_get(x_115, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_119 = x_115;
} else {
 lean_dec_ref(x_115);
 x_119 = lean_box(0);
}
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_121 = x_117;
} else {
 lean_dec_ref(x_117);
 x_121 = lean_box(0);
}
x_122 = lean_ctor_get(x_2, 3);
lean_inc(x_122);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
lean_dec(x_122);
x_124 = lean_ctor_get(x_123, 7);
lean_inc(x_124);
lean_dec(x_123);
x_125 = lean_ctor_get(x_1, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_125, 7);
lean_inc(x_126);
lean_dec(x_125);
x_127 = l_Array_append___rarg(x_124, x_126);
lean_dec(x_126);
x_128 = lean_array_get_size(x_127);
x_129 = lean_unsigned_to_nat(0u);
x_130 = lean_nat_dec_lt(x_129, x_128);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
lean_dec(x_128);
lean_dec(x_127);
x_172 = lean_ctor_get(x_2, 10);
lean_inc(x_172);
x_173 = lean_array_get_size(x_172);
x_174 = lean_nat_dec_lt(x_129, x_173);
if (x_174 == 0)
{
lean_object* x_175; 
lean_dec(x_173);
lean_dec(x_172);
x_175 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
x_131 = x_175;
goto block_171;
}
else
{
uint8_t x_176; 
x_176 = lean_nat_dec_le(x_173, x_173);
if (x_176 == 0)
{
lean_object* x_177; 
lean_dec(x_173);
lean_dec(x_172);
x_177 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
x_131 = x_177;
goto block_171;
}
else
{
size_t x_178; size_t x_179; lean_object* x_180; lean_object* x_181; 
x_178 = 0;
x_179 = lean_usize_of_nat(x_173);
lean_dec(x_173);
x_180 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
lean_inc(x_2);
x_181 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__3(x_3, x_2, x_4, x_172, x_178, x_179, x_180);
lean_dec(x_172);
x_131 = x_181;
goto block_171;
}
}
block_171:
{
lean_object* x_132; uint8_t x_133; 
x_132 = lean_array_get_size(x_131);
x_133 = lean_nat_dec_lt(x_129, x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_132);
lean_dec(x_131);
if (lean_is_scalar(x_119)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_119;
}
lean_ctor_set(x_134, 0, x_120);
lean_ctor_set(x_134, 1, x_118);
if (lean_is_scalar(x_121)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_121;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_116);
x_24 = x_135;
goto block_114;
}
else
{
uint8_t x_136; 
x_136 = lean_nat_dec_le(x_132, x_132);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_132);
lean_dec(x_131);
if (lean_is_scalar(x_119)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_119;
}
lean_ctor_set(x_137, 0, x_120);
lean_ctor_set(x_137, 1, x_118);
if (lean_is_scalar(x_121)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_121;
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_116);
x_24 = x_138;
goto block_114;
}
else
{
size_t x_139; size_t x_140; lean_object* x_141; 
lean_dec(x_121);
lean_dec(x_119);
x_139 = 0;
x_140 = lean_usize_of_nat(x_132);
lean_dec(x_132);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_141 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__2(x_131, x_139, x_140, x_120, x_8, x_9, x_10, x_11, x_118, x_116);
lean_dec(x_131);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
if (lean_obj_tag(x_142) == 0)
{
uint8_t x_143; 
x_143 = !lean_is_exclusive(x_141);
if (x_143 == 0)
{
lean_object* x_144; uint8_t x_145; 
x_144 = lean_ctor_get(x_141, 0);
lean_dec(x_144);
x_145 = !lean_is_exclusive(x_142);
if (x_145 == 0)
{
x_24 = x_141;
goto block_114;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_142, 0);
x_147 = lean_ctor_get(x_142, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_142);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
lean_ctor_set(x_141, 0, x_148);
x_24 = x_141;
goto block_114;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_149 = lean_ctor_get(x_141, 1);
lean_inc(x_149);
lean_dec(x_141);
x_150 = lean_ctor_get(x_142, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_142, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_152 = x_142;
} else {
 lean_dec_ref(x_142);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_149);
x_24 = x_154;
goto block_114;
}
}
else
{
uint8_t x_155; 
x_155 = !lean_is_exclusive(x_141);
if (x_155 == 0)
{
lean_object* x_156; uint8_t x_157; 
x_156 = lean_ctor_get(x_141, 0);
lean_dec(x_156);
x_157 = !lean_is_exclusive(x_142);
if (x_157 == 0)
{
x_24 = x_141;
goto block_114;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_142, 0);
x_159 = lean_ctor_get(x_142, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_142);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
lean_ctor_set(x_141, 0, x_160);
x_24 = x_141;
goto block_114;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_161 = lean_ctor_get(x_141, 1);
lean_inc(x_161);
lean_dec(x_141);
x_162 = lean_ctor_get(x_142, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_142, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_164 = x_142;
} else {
 lean_dec_ref(x_142);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_163);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_161);
x_24 = x_166;
goto block_114;
}
}
}
else
{
uint8_t x_167; 
x_167 = !lean_is_exclusive(x_141);
if (x_167 == 0)
{
x_24 = x_141;
goto block_114;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_141, 0);
x_169 = lean_ctor_get(x_141, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_141);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
x_24 = x_170;
goto block_114;
}
}
}
}
}
}
else
{
uint8_t x_182; 
x_182 = lean_nat_dec_le(x_128, x_128);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_224; lean_object* x_225; uint8_t x_226; 
lean_dec(x_128);
lean_dec(x_127);
x_224 = lean_ctor_get(x_2, 10);
lean_inc(x_224);
x_225 = lean_array_get_size(x_224);
x_226 = lean_nat_dec_lt(x_129, x_225);
if (x_226 == 0)
{
lean_object* x_227; 
lean_dec(x_225);
lean_dec(x_224);
x_227 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
x_183 = x_227;
goto block_223;
}
else
{
uint8_t x_228; 
x_228 = lean_nat_dec_le(x_225, x_225);
if (x_228 == 0)
{
lean_object* x_229; 
lean_dec(x_225);
lean_dec(x_224);
x_229 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
x_183 = x_229;
goto block_223;
}
else
{
size_t x_230; size_t x_231; lean_object* x_232; lean_object* x_233; 
x_230 = 0;
x_231 = lean_usize_of_nat(x_225);
lean_dec(x_225);
x_232 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
lean_inc(x_2);
x_233 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__4(x_3, x_2, x_4, x_224, x_230, x_231, x_232);
lean_dec(x_224);
x_183 = x_233;
goto block_223;
}
}
block_223:
{
lean_object* x_184; uint8_t x_185; 
x_184 = lean_array_get_size(x_183);
x_185 = lean_nat_dec_lt(x_129, x_184);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_184);
lean_dec(x_183);
if (lean_is_scalar(x_119)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_119;
}
lean_ctor_set(x_186, 0, x_120);
lean_ctor_set(x_186, 1, x_118);
if (lean_is_scalar(x_121)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_121;
}
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_116);
x_24 = x_187;
goto block_114;
}
else
{
uint8_t x_188; 
x_188 = lean_nat_dec_le(x_184, x_184);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; 
lean_dec(x_184);
lean_dec(x_183);
if (lean_is_scalar(x_119)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_119;
}
lean_ctor_set(x_189, 0, x_120);
lean_ctor_set(x_189, 1, x_118);
if (lean_is_scalar(x_121)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_121;
}
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_116);
x_24 = x_190;
goto block_114;
}
else
{
size_t x_191; size_t x_192; lean_object* x_193; 
lean_dec(x_121);
lean_dec(x_119);
x_191 = 0;
x_192 = lean_usize_of_nat(x_184);
lean_dec(x_184);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_193 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__2(x_183, x_191, x_192, x_120, x_8, x_9, x_10, x_11, x_118, x_116);
lean_dec(x_183);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
if (lean_obj_tag(x_194) == 0)
{
uint8_t x_195; 
x_195 = !lean_is_exclusive(x_193);
if (x_195 == 0)
{
lean_object* x_196; uint8_t x_197; 
x_196 = lean_ctor_get(x_193, 0);
lean_dec(x_196);
x_197 = !lean_is_exclusive(x_194);
if (x_197 == 0)
{
x_24 = x_193;
goto block_114;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_194, 0);
x_199 = lean_ctor_get(x_194, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_194);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
lean_ctor_set(x_193, 0, x_200);
x_24 = x_193;
goto block_114;
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_201 = lean_ctor_get(x_193, 1);
lean_inc(x_201);
lean_dec(x_193);
x_202 = lean_ctor_get(x_194, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_194, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_204 = x_194;
} else {
 lean_dec_ref(x_194);
 x_204 = lean_box(0);
}
if (lean_is_scalar(x_204)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_204;
}
lean_ctor_set(x_205, 0, x_202);
lean_ctor_set(x_205, 1, x_203);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_201);
x_24 = x_206;
goto block_114;
}
}
else
{
uint8_t x_207; 
x_207 = !lean_is_exclusive(x_193);
if (x_207 == 0)
{
lean_object* x_208; uint8_t x_209; 
x_208 = lean_ctor_get(x_193, 0);
lean_dec(x_208);
x_209 = !lean_is_exclusive(x_194);
if (x_209 == 0)
{
x_24 = x_193;
goto block_114;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_194, 0);
x_211 = lean_ctor_get(x_194, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_194);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
lean_ctor_set(x_193, 0, x_212);
x_24 = x_193;
goto block_114;
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_213 = lean_ctor_get(x_193, 1);
lean_inc(x_213);
lean_dec(x_193);
x_214 = lean_ctor_get(x_194, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_194, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_216 = x_194;
} else {
 lean_dec_ref(x_194);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(1, 2, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_215);
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_213);
x_24 = x_218;
goto block_114;
}
}
}
else
{
uint8_t x_219; 
x_219 = !lean_is_exclusive(x_193);
if (x_219 == 0)
{
x_24 = x_193;
goto block_114;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_193, 0);
x_221 = lean_ctor_get(x_193, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_193);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
x_24 = x_222;
goto block_114;
}
}
}
}
}
}
else
{
size_t x_234; size_t x_235; lean_object* x_236; 
lean_dec(x_121);
lean_dec(x_119);
x_234 = 0;
x_235 = lean_usize_of_nat(x_128);
lean_dec(x_128);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_236 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__5(x_2, x_127, x_234, x_235, x_120, x_8, x_9, x_10, x_11, x_118, x_116);
lean_dec(x_127);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_283; lean_object* x_284; uint8_t x_285; 
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_239 = x_236;
} else {
 lean_dec_ref(x_236);
 x_239 = lean_box(0);
}
x_240 = lean_ctor_get(x_237, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_237, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_242 = x_237;
} else {
 lean_dec_ref(x_237);
 x_242 = lean_box(0);
}
x_283 = lean_ctor_get(x_2, 10);
lean_inc(x_283);
x_284 = lean_array_get_size(x_283);
x_285 = lean_nat_dec_lt(x_129, x_284);
if (x_285 == 0)
{
lean_object* x_286; 
lean_dec(x_284);
lean_dec(x_283);
x_286 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
x_243 = x_286;
goto block_282;
}
else
{
uint8_t x_287; 
x_287 = lean_nat_dec_le(x_284, x_284);
if (x_287 == 0)
{
lean_object* x_288; 
lean_dec(x_284);
lean_dec(x_283);
x_288 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
x_243 = x_288;
goto block_282;
}
else
{
size_t x_289; lean_object* x_290; lean_object* x_291; 
x_289 = lean_usize_of_nat(x_284);
lean_dec(x_284);
x_290 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
lean_inc(x_2);
x_291 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__6(x_3, x_2, x_4, x_283, x_234, x_289, x_290);
lean_dec(x_283);
x_243 = x_291;
goto block_282;
}
}
block_282:
{
lean_object* x_244; uint8_t x_245; 
x_244 = lean_array_get_size(x_243);
x_245 = lean_nat_dec_lt(x_129, x_244);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; 
lean_dec(x_244);
lean_dec(x_243);
if (lean_is_scalar(x_242)) {
 x_246 = lean_alloc_ctor(0, 2, 0);
} else {
 x_246 = x_242;
}
lean_ctor_set(x_246, 0, x_240);
lean_ctor_set(x_246, 1, x_241);
if (lean_is_scalar(x_239)) {
 x_247 = lean_alloc_ctor(0, 2, 0);
} else {
 x_247 = x_239;
}
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_238);
x_24 = x_247;
goto block_114;
}
else
{
uint8_t x_248; 
x_248 = lean_nat_dec_le(x_244, x_244);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; 
lean_dec(x_244);
lean_dec(x_243);
if (lean_is_scalar(x_242)) {
 x_249 = lean_alloc_ctor(0, 2, 0);
} else {
 x_249 = x_242;
}
lean_ctor_set(x_249, 0, x_240);
lean_ctor_set(x_249, 1, x_241);
if (lean_is_scalar(x_239)) {
 x_250 = lean_alloc_ctor(0, 2, 0);
} else {
 x_250 = x_239;
}
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_238);
x_24 = x_250;
goto block_114;
}
else
{
size_t x_251; lean_object* x_252; 
lean_dec(x_242);
lean_dec(x_239);
x_251 = lean_usize_of_nat(x_244);
lean_dec(x_244);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_252 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__2(x_243, x_234, x_251, x_240, x_8, x_9, x_10, x_11, x_241, x_238);
lean_dec(x_243);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
if (lean_obj_tag(x_253) == 0)
{
uint8_t x_254; 
x_254 = !lean_is_exclusive(x_252);
if (x_254 == 0)
{
lean_object* x_255; uint8_t x_256; 
x_255 = lean_ctor_get(x_252, 0);
lean_dec(x_255);
x_256 = !lean_is_exclusive(x_253);
if (x_256 == 0)
{
x_24 = x_252;
goto block_114;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = lean_ctor_get(x_253, 0);
x_258 = lean_ctor_get(x_253, 1);
lean_inc(x_258);
lean_inc(x_257);
lean_dec(x_253);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
lean_ctor_set(x_252, 0, x_259);
x_24 = x_252;
goto block_114;
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_260 = lean_ctor_get(x_252, 1);
lean_inc(x_260);
lean_dec(x_252);
x_261 = lean_ctor_get(x_253, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_253, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_263 = x_253;
} else {
 lean_dec_ref(x_253);
 x_263 = lean_box(0);
}
if (lean_is_scalar(x_263)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_263;
}
lean_ctor_set(x_264, 0, x_261);
lean_ctor_set(x_264, 1, x_262);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_260);
x_24 = x_265;
goto block_114;
}
}
else
{
uint8_t x_266; 
x_266 = !lean_is_exclusive(x_252);
if (x_266 == 0)
{
lean_object* x_267; uint8_t x_268; 
x_267 = lean_ctor_get(x_252, 0);
lean_dec(x_267);
x_268 = !lean_is_exclusive(x_253);
if (x_268 == 0)
{
x_24 = x_252;
goto block_114;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_253, 0);
x_270 = lean_ctor_get(x_253, 1);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_253);
x_271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_270);
lean_ctor_set(x_252, 0, x_271);
x_24 = x_252;
goto block_114;
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_272 = lean_ctor_get(x_252, 1);
lean_inc(x_272);
lean_dec(x_252);
x_273 = lean_ctor_get(x_253, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_253, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_275 = x_253;
} else {
 lean_dec_ref(x_253);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_276 = lean_alloc_ctor(1, 2, 0);
} else {
 x_276 = x_275;
}
lean_ctor_set(x_276, 0, x_273);
lean_ctor_set(x_276, 1, x_274);
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_272);
x_24 = x_277;
goto block_114;
}
}
}
else
{
uint8_t x_278; 
x_278 = !lean_is_exclusive(x_252);
if (x_278 == 0)
{
x_24 = x_252;
goto block_114;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_279 = lean_ctor_get(x_252, 0);
x_280 = lean_ctor_get(x_252, 1);
lean_inc(x_280);
lean_inc(x_279);
lean_dec(x_252);
x_281 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_281, 0, x_279);
lean_ctor_set(x_281, 1, x_280);
x_24 = x_281;
goto block_114;
}
}
}
}
}
}
else
{
uint8_t x_292; 
x_292 = !lean_is_exclusive(x_236);
if (x_292 == 0)
{
lean_object* x_293; uint8_t x_294; 
x_293 = lean_ctor_get(x_236, 0);
lean_dec(x_293);
x_294 = !lean_is_exclusive(x_237);
if (x_294 == 0)
{
x_24 = x_236;
goto block_114;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_295 = lean_ctor_get(x_237, 0);
x_296 = lean_ctor_get(x_237, 1);
lean_inc(x_296);
lean_inc(x_295);
lean_dec(x_237);
x_297 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_297, 0, x_295);
lean_ctor_set(x_297, 1, x_296);
lean_ctor_set(x_236, 0, x_297);
x_24 = x_236;
goto block_114;
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_298 = lean_ctor_get(x_236, 1);
lean_inc(x_298);
lean_dec(x_236);
x_299 = lean_ctor_get(x_237, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_237, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_301 = x_237;
} else {
 lean_dec_ref(x_237);
 x_301 = lean_box(0);
}
if (lean_is_scalar(x_301)) {
 x_302 = lean_alloc_ctor(1, 2, 0);
} else {
 x_302 = x_301;
}
lean_ctor_set(x_302, 0, x_299);
lean_ctor_set(x_302, 1, x_300);
x_303 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_298);
x_24 = x_303;
goto block_114;
}
}
}
else
{
uint8_t x_304; 
x_304 = !lean_is_exclusive(x_236);
if (x_304 == 0)
{
x_24 = x_236;
goto block_114;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_305 = lean_ctor_get(x_236, 0);
x_306 = lean_ctor_get(x_236, 1);
lean_inc(x_306);
lean_inc(x_305);
lean_dec(x_236);
x_307 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_307, 0, x_305);
lean_ctor_set(x_307, 1, x_306);
x_24 = x_307;
goto block_114;
}
}
}
}
}
else
{
uint8_t x_308; 
x_308 = !lean_is_exclusive(x_115);
if (x_308 == 0)
{
lean_object* x_309; 
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_115);
lean_ctor_set(x_309, 1, x_116);
x_24 = x_309;
goto block_114;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_310 = lean_ctor_get(x_115, 0);
x_311 = lean_ctor_get(x_115, 1);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_115);
x_312 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_312, 0, x_310);
lean_ctor_set(x_312, 1, x_311);
x_313 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_116);
x_24 = x_313;
goto block_114;
}
}
}
block_368:
{
if (lean_obj_tag(x_315) == 0)
{
uint8_t x_317; 
x_317 = !lean_is_exclusive(x_315);
if (x_317 == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; uint8_t x_328; 
x_318 = lean_ctor_get(x_315, 0);
x_319 = lean_ctor_get(x_315, 1);
x_320 = l_Lean_NameSet_empty;
x_321 = lean_box(0);
x_322 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_320, x_5, x_321);
x_323 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_322);
lean_ctor_set(x_324, 1, x_323);
x_325 = lean_ctor_get(x_318, 1);
lean_inc(x_325);
lean_dec(x_318);
x_326 = lean_array_get_size(x_325);
x_327 = lean_unsigned_to_nat(0u);
x_328 = lean_nat_dec_lt(x_327, x_326);
if (x_328 == 0)
{
lean_dec(x_326);
lean_dec(x_325);
lean_dec(x_6);
lean_ctor_set(x_315, 0, x_324);
x_115 = x_315;
x_116 = x_316;
goto block_314;
}
else
{
uint8_t x_329; 
x_329 = lean_nat_dec_le(x_326, x_326);
if (x_329 == 0)
{
lean_dec(x_326);
lean_dec(x_325);
lean_dec(x_6);
lean_ctor_set(x_315, 0, x_324);
x_115 = x_315;
x_116 = x_316;
goto block_314;
}
else
{
size_t x_330; size_t x_331; lean_object* x_332; 
lean_free_object(x_315);
x_330 = 0;
x_331 = lean_usize_of_nat(x_326);
lean_dec(x_326);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_332 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__7(x_6, x_325, x_330, x_331, x_324, x_8, x_9, x_10, x_11, x_319, x_316);
lean_dec(x_325);
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_333; lean_object* x_334; 
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
lean_dec(x_332);
x_115 = x_333;
x_116 = x_334;
goto block_314;
}
else
{
uint8_t x_335; 
x_335 = !lean_is_exclusive(x_332);
if (x_335 == 0)
{
x_24 = x_332;
goto block_114;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_336 = lean_ctor_get(x_332, 0);
x_337 = lean_ctor_get(x_332, 1);
lean_inc(x_337);
lean_inc(x_336);
lean_dec(x_332);
x_338 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_338, 0, x_336);
lean_ctor_set(x_338, 1, x_337);
x_24 = x_338;
goto block_114;
}
}
}
}
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; 
x_339 = lean_ctor_get(x_315, 0);
x_340 = lean_ctor_get(x_315, 1);
lean_inc(x_340);
lean_inc(x_339);
lean_dec(x_315);
x_341 = l_Lean_NameSet_empty;
x_342 = lean_box(0);
x_343 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_341, x_5, x_342);
x_344 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
x_345 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_345, 0, x_343);
lean_ctor_set(x_345, 1, x_344);
x_346 = lean_ctor_get(x_339, 1);
lean_inc(x_346);
lean_dec(x_339);
x_347 = lean_array_get_size(x_346);
x_348 = lean_unsigned_to_nat(0u);
x_349 = lean_nat_dec_lt(x_348, x_347);
if (x_349 == 0)
{
lean_object* x_350; 
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_6);
x_350 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_350, 0, x_345);
lean_ctor_set(x_350, 1, x_340);
x_115 = x_350;
x_116 = x_316;
goto block_314;
}
else
{
uint8_t x_351; 
x_351 = lean_nat_dec_le(x_347, x_347);
if (x_351 == 0)
{
lean_object* x_352; 
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_6);
x_352 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_352, 0, x_345);
lean_ctor_set(x_352, 1, x_340);
x_115 = x_352;
x_116 = x_316;
goto block_314;
}
else
{
size_t x_353; size_t x_354; lean_object* x_355; 
x_353 = 0;
x_354 = lean_usize_of_nat(x_347);
lean_dec(x_347);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_355 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__7(x_6, x_346, x_353, x_354, x_345, x_8, x_9, x_10, x_11, x_340, x_316);
lean_dec(x_346);
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_356; lean_object* x_357; 
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_355, 1);
lean_inc(x_357);
lean_dec(x_355);
x_115 = x_356;
x_116 = x_357;
goto block_314;
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_358 = lean_ctor_get(x_355, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_355, 1);
lean_inc(x_359);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 x_360 = x_355;
} else {
 lean_dec_ref(x_355);
 x_360 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_361 = lean_alloc_ctor(1, 2, 0);
} else {
 x_361 = x_360;
}
lean_ctor_set(x_361, 0, x_358);
lean_ctor_set(x_361, 1, x_359);
x_24 = x_361;
goto block_114;
}
}
}
}
}
else
{
uint8_t x_362; 
lean_dec(x_6);
lean_dec(x_5);
x_362 = !lean_is_exclusive(x_315);
if (x_362 == 0)
{
lean_object* x_363; 
x_363 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_363, 0, x_315);
lean_ctor_set(x_363, 1, x_316);
x_24 = x_363;
goto block_114;
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_364 = lean_ctor_get(x_315, 0);
x_365 = lean_ctor_get(x_315, 1);
lean_inc(x_365);
lean_inc(x_364);
lean_dec(x_315);
x_366 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_366, 0, x_364);
lean_ctor_set(x_366, 1, x_365);
x_367 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_316);
x_24 = x_367;
goto block_114;
}
}
}
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_438; lean_object* x_439; lean_object* x_602; lean_object* x_603; lean_object* x_634; lean_object* x_635; uint8_t x_636; 
x_385 = lean_ctor_get(x_19, 0);
x_386 = lean_ctor_get(x_19, 1);
lean_inc(x_386);
lean_inc(x_385);
lean_dec(x_19);
x_634 = lean_array_get_size(x_17);
x_635 = lean_unsigned_to_nat(0u);
x_636 = lean_nat_dec_lt(x_635, x_634);
if (x_636 == 0)
{
lean_object* x_637; lean_object* x_638; 
lean_dec(x_634);
lean_dec(x_17);
x_637 = l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
x_638 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_638, 0, x_637);
lean_ctor_set(x_638, 1, x_386);
x_602 = x_638;
x_603 = x_20;
goto block_633;
}
else
{
uint8_t x_639; 
x_639 = lean_nat_dec_le(x_634, x_634);
if (x_639 == 0)
{
lean_object* x_640; lean_object* x_641; 
lean_dec(x_634);
lean_dec(x_17);
x_640 = l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
x_641 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_641, 0, x_640);
lean_ctor_set(x_641, 1, x_386);
x_602 = x_641;
x_603 = x_20;
goto block_633;
}
else
{
size_t x_642; size_t x_643; lean_object* x_644; lean_object* x_645; 
x_642 = 0;
x_643 = lean_usize_of_nat(x_634);
lean_dec(x_634);
x_644 = l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_645 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__11(x_17, x_642, x_643, x_644, x_8, x_9, x_10, x_11, x_386, x_20);
lean_dec(x_17);
if (lean_obj_tag(x_645) == 0)
{
lean_object* x_646; lean_object* x_647; 
x_646 = lean_ctor_get(x_645, 0);
lean_inc(x_646);
x_647 = lean_ctor_get(x_645, 1);
lean_inc(x_647);
lean_dec(x_645);
x_602 = x_646;
x_603 = x_647;
goto block_633;
}
else
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; 
lean_dec(x_6);
lean_dec(x_5);
x_648 = lean_ctor_get(x_645, 0);
lean_inc(x_648);
x_649 = lean_ctor_get(x_645, 1);
lean_inc(x_649);
if (lean_is_exclusive(x_645)) {
 lean_ctor_release(x_645, 0);
 lean_ctor_release(x_645, 1);
 x_650 = x_645;
} else {
 lean_dec_ref(x_645);
 x_650 = lean_box(0);
}
if (lean_is_scalar(x_650)) {
 x_651 = lean_alloc_ctor(1, 2, 0);
} else {
 x_651 = x_650;
}
lean_ctor_set(x_651, 0, x_648);
lean_ctor_set(x_651, 1, x_649);
x_387 = x_651;
goto block_437;
}
}
}
block_437:
{
if (lean_obj_tag(x_387) == 0)
{
lean_object* x_388; 
x_388 = lean_ctor_get(x_387, 0);
lean_inc(x_388);
if (lean_obj_tag(x_388) == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_413; uint8_t x_414; lean_object* x_415; lean_object* x_416; 
x_389 = lean_ctor_get(x_387, 1);
lean_inc(x_389);
lean_dec(x_387);
x_390 = lean_ctor_get(x_388, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_388, 1);
lean_inc(x_391);
if (lean_is_exclusive(x_388)) {
 lean_ctor_release(x_388, 0);
 lean_ctor_release(x_388, 1);
 x_392 = x_388;
} else {
 lean_dec_ref(x_388);
 x_392 = lean_box(0);
}
x_393 = lean_ctor_get(x_1, 4);
lean_inc(x_393);
x_394 = lean_ctor_get(x_2, 1);
lean_inc(x_394);
x_395 = lean_ctor_get(x_2, 3);
lean_inc(x_395);
lean_dec(x_2);
x_396 = lean_ctor_get(x_395, 6);
lean_inc(x_396);
x_397 = l_Lake_joinRelative(x_394, x_396);
lean_dec(x_396);
x_398 = lean_ctor_get(x_395, 8);
lean_inc(x_398);
x_399 = l_Lake_joinRelative(x_397, x_398);
lean_dec(x_398);
x_400 = l_Lake_nameToSharedLib(x_393);
x_401 = l_Lake_joinRelative(x_399, x_400);
lean_dec(x_400);
x_402 = lean_ctor_get(x_395, 1);
lean_inc(x_402);
lean_dec(x_395);
x_403 = lean_ctor_get(x_402, 9);
lean_inc(x_403);
x_404 = lean_ctor_get(x_1, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_404, 9);
lean_inc(x_405);
x_406 = l_Array_append___rarg(x_403, x_405);
lean_dec(x_405);
x_407 = lean_ctor_get(x_402, 8);
lean_inc(x_407);
lean_dec(x_402);
x_408 = lean_ctor_get(x_404, 8);
lean_inc(x_408);
lean_dec(x_404);
x_409 = l_Array_append___rarg(x_407, x_408);
lean_dec(x_408);
x_410 = lean_ctor_get(x_1, 2);
lean_inc(x_410);
lean_dec(x_1);
x_411 = lean_array_get_size(x_410);
lean_dec(x_410);
x_412 = lean_unsigned_to_nat(1u);
x_413 = lean_nat_dec_eq(x_411, x_412);
lean_dec(x_411);
x_414 = l_System_Platform_isWindows;
x_415 = l_Lake_BuildTrace_nil;
x_416 = l_Lake_buildLeanSharedLib(x_393, x_401, x_385, x_390, x_406, x_409, x_413, x_414, x_8, x_9, x_10, x_11, x_415, x_389);
lean_dec(x_385);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_416, 1);
lean_inc(x_418);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 x_419 = x_416;
} else {
 lean_dec_ref(x_416);
 x_419 = lean_box(0);
}
if (lean_is_scalar(x_392)) {
 x_420 = lean_alloc_ctor(0, 2, 0);
} else {
 x_420 = x_392;
}
lean_ctor_set(x_420, 0, x_417);
lean_ctor_set(x_420, 1, x_391);
if (lean_is_scalar(x_419)) {
 x_421 = lean_alloc_ctor(0, 2, 0);
} else {
 x_421 = x_419;
}
lean_ctor_set(x_421, 0, x_420);
lean_ctor_set(x_421, 1, x_418);
return x_421;
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
lean_dec(x_392);
lean_dec(x_391);
x_422 = lean_ctor_get(x_416, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_416, 1);
lean_inc(x_423);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 x_424 = x_416;
} else {
 lean_dec_ref(x_416);
 x_424 = lean_box(0);
}
if (lean_is_scalar(x_424)) {
 x_425 = lean_alloc_ctor(1, 2, 0);
} else {
 x_425 = x_424;
}
lean_ctor_set(x_425, 0, x_422);
lean_ctor_set(x_425, 1, x_423);
return x_425;
}
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
lean_dec(x_385);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_426 = lean_ctor_get(x_387, 1);
lean_inc(x_426);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 x_427 = x_387;
} else {
 lean_dec_ref(x_387);
 x_427 = lean_box(0);
}
x_428 = lean_ctor_get(x_388, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_388, 1);
lean_inc(x_429);
if (lean_is_exclusive(x_388)) {
 lean_ctor_release(x_388, 0);
 lean_ctor_release(x_388, 1);
 x_430 = x_388;
} else {
 lean_dec_ref(x_388);
 x_430 = lean_box(0);
}
if (lean_is_scalar(x_430)) {
 x_431 = lean_alloc_ctor(1, 2, 0);
} else {
 x_431 = x_430;
}
lean_ctor_set(x_431, 0, x_428);
lean_ctor_set(x_431, 1, x_429);
if (lean_is_scalar(x_427)) {
 x_432 = lean_alloc_ctor(0, 2, 0);
} else {
 x_432 = x_427;
}
lean_ctor_set(x_432, 0, x_431);
lean_ctor_set(x_432, 1, x_426);
return x_432;
}
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
lean_dec(x_385);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_433 = lean_ctor_get(x_387, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_387, 1);
lean_inc(x_434);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 x_435 = x_387;
} else {
 lean_dec_ref(x_387);
 x_435 = lean_box(0);
}
if (lean_is_scalar(x_435)) {
 x_436 = lean_alloc_ctor(1, 2, 0);
} else {
 x_436 = x_435;
}
lean_ctor_set(x_436, 0, x_433);
lean_ctor_set(x_436, 1, x_434);
return x_436;
}
}
block_601:
{
if (lean_obj_tag(x_438) == 0)
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; uint8_t x_453; 
x_440 = lean_ctor_get(x_438, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_438, 1);
lean_inc(x_441);
if (lean_is_exclusive(x_438)) {
 lean_ctor_release(x_438, 0);
 lean_ctor_release(x_438, 1);
 x_442 = x_438;
} else {
 lean_dec_ref(x_438);
 x_442 = lean_box(0);
}
x_443 = lean_ctor_get(x_440, 1);
lean_inc(x_443);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 lean_ctor_release(x_440, 1);
 x_444 = x_440;
} else {
 lean_dec_ref(x_440);
 x_444 = lean_box(0);
}
x_445 = lean_ctor_get(x_2, 3);
lean_inc(x_445);
x_446 = lean_ctor_get(x_445, 1);
lean_inc(x_446);
lean_dec(x_445);
x_447 = lean_ctor_get(x_446, 7);
lean_inc(x_447);
lean_dec(x_446);
x_448 = lean_ctor_get(x_1, 0);
lean_inc(x_448);
x_449 = lean_ctor_get(x_448, 7);
lean_inc(x_449);
lean_dec(x_448);
x_450 = l_Array_append___rarg(x_447, x_449);
lean_dec(x_449);
x_451 = lean_array_get_size(x_450);
x_452 = lean_unsigned_to_nat(0u);
x_453 = lean_nat_dec_lt(x_452, x_451);
if (x_453 == 0)
{
lean_object* x_454; lean_object* x_485; lean_object* x_486; uint8_t x_487; 
lean_dec(x_451);
lean_dec(x_450);
x_485 = lean_ctor_get(x_2, 10);
lean_inc(x_485);
x_486 = lean_array_get_size(x_485);
x_487 = lean_nat_dec_lt(x_452, x_486);
if (x_487 == 0)
{
lean_object* x_488; 
lean_dec(x_486);
lean_dec(x_485);
x_488 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
x_454 = x_488;
goto block_484;
}
else
{
uint8_t x_489; 
x_489 = lean_nat_dec_le(x_486, x_486);
if (x_489 == 0)
{
lean_object* x_490; 
lean_dec(x_486);
lean_dec(x_485);
x_490 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
x_454 = x_490;
goto block_484;
}
else
{
size_t x_491; size_t x_492; lean_object* x_493; lean_object* x_494; 
x_491 = 0;
x_492 = lean_usize_of_nat(x_486);
lean_dec(x_486);
x_493 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
lean_inc(x_2);
x_494 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__3(x_3, x_2, x_4, x_485, x_491, x_492, x_493);
lean_dec(x_485);
x_454 = x_494;
goto block_484;
}
}
block_484:
{
lean_object* x_455; uint8_t x_456; 
x_455 = lean_array_get_size(x_454);
x_456 = lean_nat_dec_lt(x_452, x_455);
if (x_456 == 0)
{
lean_object* x_457; lean_object* x_458; 
lean_dec(x_455);
lean_dec(x_454);
if (lean_is_scalar(x_442)) {
 x_457 = lean_alloc_ctor(0, 2, 0);
} else {
 x_457 = x_442;
}
lean_ctor_set(x_457, 0, x_443);
lean_ctor_set(x_457, 1, x_441);
if (lean_is_scalar(x_444)) {
 x_458 = lean_alloc_ctor(0, 2, 0);
} else {
 x_458 = x_444;
}
lean_ctor_set(x_458, 0, x_457);
lean_ctor_set(x_458, 1, x_439);
x_387 = x_458;
goto block_437;
}
else
{
uint8_t x_459; 
x_459 = lean_nat_dec_le(x_455, x_455);
if (x_459 == 0)
{
lean_object* x_460; lean_object* x_461; 
lean_dec(x_455);
lean_dec(x_454);
if (lean_is_scalar(x_442)) {
 x_460 = lean_alloc_ctor(0, 2, 0);
} else {
 x_460 = x_442;
}
lean_ctor_set(x_460, 0, x_443);
lean_ctor_set(x_460, 1, x_441);
if (lean_is_scalar(x_444)) {
 x_461 = lean_alloc_ctor(0, 2, 0);
} else {
 x_461 = x_444;
}
lean_ctor_set(x_461, 0, x_460);
lean_ctor_set(x_461, 1, x_439);
x_387 = x_461;
goto block_437;
}
else
{
size_t x_462; size_t x_463; lean_object* x_464; 
lean_dec(x_444);
lean_dec(x_442);
x_462 = 0;
x_463 = lean_usize_of_nat(x_455);
lean_dec(x_455);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_464 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__2(x_454, x_462, x_463, x_443, x_8, x_9, x_10, x_11, x_441, x_439);
lean_dec(x_454);
if (lean_obj_tag(x_464) == 0)
{
lean_object* x_465; 
x_465 = lean_ctor_get(x_464, 0);
lean_inc(x_465);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_466 = lean_ctor_get(x_464, 1);
lean_inc(x_466);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 x_467 = x_464;
} else {
 lean_dec_ref(x_464);
 x_467 = lean_box(0);
}
x_468 = lean_ctor_get(x_465, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_465, 1);
lean_inc(x_469);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 x_470 = x_465;
} else {
 lean_dec_ref(x_465);
 x_470 = lean_box(0);
}
if (lean_is_scalar(x_470)) {
 x_471 = lean_alloc_ctor(0, 2, 0);
} else {
 x_471 = x_470;
}
lean_ctor_set(x_471, 0, x_468);
lean_ctor_set(x_471, 1, x_469);
if (lean_is_scalar(x_467)) {
 x_472 = lean_alloc_ctor(0, 2, 0);
} else {
 x_472 = x_467;
}
lean_ctor_set(x_472, 0, x_471);
lean_ctor_set(x_472, 1, x_466);
x_387 = x_472;
goto block_437;
}
else
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; 
x_473 = lean_ctor_get(x_464, 1);
lean_inc(x_473);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 x_474 = x_464;
} else {
 lean_dec_ref(x_464);
 x_474 = lean_box(0);
}
x_475 = lean_ctor_get(x_465, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_465, 1);
lean_inc(x_476);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 x_477 = x_465;
} else {
 lean_dec_ref(x_465);
 x_477 = lean_box(0);
}
if (lean_is_scalar(x_477)) {
 x_478 = lean_alloc_ctor(1, 2, 0);
} else {
 x_478 = x_477;
}
lean_ctor_set(x_478, 0, x_475);
lean_ctor_set(x_478, 1, x_476);
if (lean_is_scalar(x_474)) {
 x_479 = lean_alloc_ctor(0, 2, 0);
} else {
 x_479 = x_474;
}
lean_ctor_set(x_479, 0, x_478);
lean_ctor_set(x_479, 1, x_473);
x_387 = x_479;
goto block_437;
}
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_480 = lean_ctor_get(x_464, 0);
lean_inc(x_480);
x_481 = lean_ctor_get(x_464, 1);
lean_inc(x_481);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 x_482 = x_464;
} else {
 lean_dec_ref(x_464);
 x_482 = lean_box(0);
}
if (lean_is_scalar(x_482)) {
 x_483 = lean_alloc_ctor(1, 2, 0);
} else {
 x_483 = x_482;
}
lean_ctor_set(x_483, 0, x_480);
lean_ctor_set(x_483, 1, x_481);
x_387 = x_483;
goto block_437;
}
}
}
}
}
else
{
uint8_t x_495; 
x_495 = lean_nat_dec_le(x_451, x_451);
if (x_495 == 0)
{
lean_object* x_496; lean_object* x_527; lean_object* x_528; uint8_t x_529; 
lean_dec(x_451);
lean_dec(x_450);
x_527 = lean_ctor_get(x_2, 10);
lean_inc(x_527);
x_528 = lean_array_get_size(x_527);
x_529 = lean_nat_dec_lt(x_452, x_528);
if (x_529 == 0)
{
lean_object* x_530; 
lean_dec(x_528);
lean_dec(x_527);
x_530 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
x_496 = x_530;
goto block_526;
}
else
{
uint8_t x_531; 
x_531 = lean_nat_dec_le(x_528, x_528);
if (x_531 == 0)
{
lean_object* x_532; 
lean_dec(x_528);
lean_dec(x_527);
x_532 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
x_496 = x_532;
goto block_526;
}
else
{
size_t x_533; size_t x_534; lean_object* x_535; lean_object* x_536; 
x_533 = 0;
x_534 = lean_usize_of_nat(x_528);
lean_dec(x_528);
x_535 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
lean_inc(x_2);
x_536 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__4(x_3, x_2, x_4, x_527, x_533, x_534, x_535);
lean_dec(x_527);
x_496 = x_536;
goto block_526;
}
}
block_526:
{
lean_object* x_497; uint8_t x_498; 
x_497 = lean_array_get_size(x_496);
x_498 = lean_nat_dec_lt(x_452, x_497);
if (x_498 == 0)
{
lean_object* x_499; lean_object* x_500; 
lean_dec(x_497);
lean_dec(x_496);
if (lean_is_scalar(x_442)) {
 x_499 = lean_alloc_ctor(0, 2, 0);
} else {
 x_499 = x_442;
}
lean_ctor_set(x_499, 0, x_443);
lean_ctor_set(x_499, 1, x_441);
if (lean_is_scalar(x_444)) {
 x_500 = lean_alloc_ctor(0, 2, 0);
} else {
 x_500 = x_444;
}
lean_ctor_set(x_500, 0, x_499);
lean_ctor_set(x_500, 1, x_439);
x_387 = x_500;
goto block_437;
}
else
{
uint8_t x_501; 
x_501 = lean_nat_dec_le(x_497, x_497);
if (x_501 == 0)
{
lean_object* x_502; lean_object* x_503; 
lean_dec(x_497);
lean_dec(x_496);
if (lean_is_scalar(x_442)) {
 x_502 = lean_alloc_ctor(0, 2, 0);
} else {
 x_502 = x_442;
}
lean_ctor_set(x_502, 0, x_443);
lean_ctor_set(x_502, 1, x_441);
if (lean_is_scalar(x_444)) {
 x_503 = lean_alloc_ctor(0, 2, 0);
} else {
 x_503 = x_444;
}
lean_ctor_set(x_503, 0, x_502);
lean_ctor_set(x_503, 1, x_439);
x_387 = x_503;
goto block_437;
}
else
{
size_t x_504; size_t x_505; lean_object* x_506; 
lean_dec(x_444);
lean_dec(x_442);
x_504 = 0;
x_505 = lean_usize_of_nat(x_497);
lean_dec(x_497);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_506 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__2(x_496, x_504, x_505, x_443, x_8, x_9, x_10, x_11, x_441, x_439);
lean_dec(x_496);
if (lean_obj_tag(x_506) == 0)
{
lean_object* x_507; 
x_507 = lean_ctor_get(x_506, 0);
lean_inc(x_507);
if (lean_obj_tag(x_507) == 0)
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
x_508 = lean_ctor_get(x_506, 1);
lean_inc(x_508);
if (lean_is_exclusive(x_506)) {
 lean_ctor_release(x_506, 0);
 lean_ctor_release(x_506, 1);
 x_509 = x_506;
} else {
 lean_dec_ref(x_506);
 x_509 = lean_box(0);
}
x_510 = lean_ctor_get(x_507, 0);
lean_inc(x_510);
x_511 = lean_ctor_get(x_507, 1);
lean_inc(x_511);
if (lean_is_exclusive(x_507)) {
 lean_ctor_release(x_507, 0);
 lean_ctor_release(x_507, 1);
 x_512 = x_507;
} else {
 lean_dec_ref(x_507);
 x_512 = lean_box(0);
}
if (lean_is_scalar(x_512)) {
 x_513 = lean_alloc_ctor(0, 2, 0);
} else {
 x_513 = x_512;
}
lean_ctor_set(x_513, 0, x_510);
lean_ctor_set(x_513, 1, x_511);
if (lean_is_scalar(x_509)) {
 x_514 = lean_alloc_ctor(0, 2, 0);
} else {
 x_514 = x_509;
}
lean_ctor_set(x_514, 0, x_513);
lean_ctor_set(x_514, 1, x_508);
x_387 = x_514;
goto block_437;
}
else
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
x_515 = lean_ctor_get(x_506, 1);
lean_inc(x_515);
if (lean_is_exclusive(x_506)) {
 lean_ctor_release(x_506, 0);
 lean_ctor_release(x_506, 1);
 x_516 = x_506;
} else {
 lean_dec_ref(x_506);
 x_516 = lean_box(0);
}
x_517 = lean_ctor_get(x_507, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_507, 1);
lean_inc(x_518);
if (lean_is_exclusive(x_507)) {
 lean_ctor_release(x_507, 0);
 lean_ctor_release(x_507, 1);
 x_519 = x_507;
} else {
 lean_dec_ref(x_507);
 x_519 = lean_box(0);
}
if (lean_is_scalar(x_519)) {
 x_520 = lean_alloc_ctor(1, 2, 0);
} else {
 x_520 = x_519;
}
lean_ctor_set(x_520, 0, x_517);
lean_ctor_set(x_520, 1, x_518);
if (lean_is_scalar(x_516)) {
 x_521 = lean_alloc_ctor(0, 2, 0);
} else {
 x_521 = x_516;
}
lean_ctor_set(x_521, 0, x_520);
lean_ctor_set(x_521, 1, x_515);
x_387 = x_521;
goto block_437;
}
}
else
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; 
x_522 = lean_ctor_get(x_506, 0);
lean_inc(x_522);
x_523 = lean_ctor_get(x_506, 1);
lean_inc(x_523);
if (lean_is_exclusive(x_506)) {
 lean_ctor_release(x_506, 0);
 lean_ctor_release(x_506, 1);
 x_524 = x_506;
} else {
 lean_dec_ref(x_506);
 x_524 = lean_box(0);
}
if (lean_is_scalar(x_524)) {
 x_525 = lean_alloc_ctor(1, 2, 0);
} else {
 x_525 = x_524;
}
lean_ctor_set(x_525, 0, x_522);
lean_ctor_set(x_525, 1, x_523);
x_387 = x_525;
goto block_437;
}
}
}
}
}
else
{
size_t x_537; size_t x_538; lean_object* x_539; 
lean_dec(x_444);
lean_dec(x_442);
x_537 = 0;
x_538 = lean_usize_of_nat(x_451);
lean_dec(x_451);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_539 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__5(x_2, x_450, x_537, x_538, x_443, x_8, x_9, x_10, x_11, x_441, x_439);
lean_dec(x_450);
if (lean_obj_tag(x_539) == 0)
{
lean_object* x_540; 
x_540 = lean_ctor_get(x_539, 0);
lean_inc(x_540);
if (lean_obj_tag(x_540) == 0)
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_576; lean_object* x_577; uint8_t x_578; 
x_541 = lean_ctor_get(x_539, 1);
lean_inc(x_541);
if (lean_is_exclusive(x_539)) {
 lean_ctor_release(x_539, 0);
 lean_ctor_release(x_539, 1);
 x_542 = x_539;
} else {
 lean_dec_ref(x_539);
 x_542 = lean_box(0);
}
x_543 = lean_ctor_get(x_540, 0);
lean_inc(x_543);
x_544 = lean_ctor_get(x_540, 1);
lean_inc(x_544);
if (lean_is_exclusive(x_540)) {
 lean_ctor_release(x_540, 0);
 lean_ctor_release(x_540, 1);
 x_545 = x_540;
} else {
 lean_dec_ref(x_540);
 x_545 = lean_box(0);
}
x_576 = lean_ctor_get(x_2, 10);
lean_inc(x_576);
x_577 = lean_array_get_size(x_576);
x_578 = lean_nat_dec_lt(x_452, x_577);
if (x_578 == 0)
{
lean_object* x_579; 
lean_dec(x_577);
lean_dec(x_576);
x_579 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
x_546 = x_579;
goto block_575;
}
else
{
uint8_t x_580; 
x_580 = lean_nat_dec_le(x_577, x_577);
if (x_580 == 0)
{
lean_object* x_581; 
lean_dec(x_577);
lean_dec(x_576);
x_581 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
x_546 = x_581;
goto block_575;
}
else
{
size_t x_582; lean_object* x_583; lean_object* x_584; 
x_582 = lean_usize_of_nat(x_577);
lean_dec(x_577);
x_583 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
lean_inc(x_2);
x_584 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__6(x_3, x_2, x_4, x_576, x_537, x_582, x_583);
lean_dec(x_576);
x_546 = x_584;
goto block_575;
}
}
block_575:
{
lean_object* x_547; uint8_t x_548; 
x_547 = lean_array_get_size(x_546);
x_548 = lean_nat_dec_lt(x_452, x_547);
if (x_548 == 0)
{
lean_object* x_549; lean_object* x_550; 
lean_dec(x_547);
lean_dec(x_546);
if (lean_is_scalar(x_545)) {
 x_549 = lean_alloc_ctor(0, 2, 0);
} else {
 x_549 = x_545;
}
lean_ctor_set(x_549, 0, x_543);
lean_ctor_set(x_549, 1, x_544);
if (lean_is_scalar(x_542)) {
 x_550 = lean_alloc_ctor(0, 2, 0);
} else {
 x_550 = x_542;
}
lean_ctor_set(x_550, 0, x_549);
lean_ctor_set(x_550, 1, x_541);
x_387 = x_550;
goto block_437;
}
else
{
uint8_t x_551; 
x_551 = lean_nat_dec_le(x_547, x_547);
if (x_551 == 0)
{
lean_object* x_552; lean_object* x_553; 
lean_dec(x_547);
lean_dec(x_546);
if (lean_is_scalar(x_545)) {
 x_552 = lean_alloc_ctor(0, 2, 0);
} else {
 x_552 = x_545;
}
lean_ctor_set(x_552, 0, x_543);
lean_ctor_set(x_552, 1, x_544);
if (lean_is_scalar(x_542)) {
 x_553 = lean_alloc_ctor(0, 2, 0);
} else {
 x_553 = x_542;
}
lean_ctor_set(x_553, 0, x_552);
lean_ctor_set(x_553, 1, x_541);
x_387 = x_553;
goto block_437;
}
else
{
size_t x_554; lean_object* x_555; 
lean_dec(x_545);
lean_dec(x_542);
x_554 = lean_usize_of_nat(x_547);
lean_dec(x_547);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_555 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__2(x_546, x_537, x_554, x_543, x_8, x_9, x_10, x_11, x_544, x_541);
lean_dec(x_546);
if (lean_obj_tag(x_555) == 0)
{
lean_object* x_556; 
x_556 = lean_ctor_get(x_555, 0);
lean_inc(x_556);
if (lean_obj_tag(x_556) == 0)
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; 
x_557 = lean_ctor_get(x_555, 1);
lean_inc(x_557);
if (lean_is_exclusive(x_555)) {
 lean_ctor_release(x_555, 0);
 lean_ctor_release(x_555, 1);
 x_558 = x_555;
} else {
 lean_dec_ref(x_555);
 x_558 = lean_box(0);
}
x_559 = lean_ctor_get(x_556, 0);
lean_inc(x_559);
x_560 = lean_ctor_get(x_556, 1);
lean_inc(x_560);
if (lean_is_exclusive(x_556)) {
 lean_ctor_release(x_556, 0);
 lean_ctor_release(x_556, 1);
 x_561 = x_556;
} else {
 lean_dec_ref(x_556);
 x_561 = lean_box(0);
}
if (lean_is_scalar(x_561)) {
 x_562 = lean_alloc_ctor(0, 2, 0);
} else {
 x_562 = x_561;
}
lean_ctor_set(x_562, 0, x_559);
lean_ctor_set(x_562, 1, x_560);
if (lean_is_scalar(x_558)) {
 x_563 = lean_alloc_ctor(0, 2, 0);
} else {
 x_563 = x_558;
}
lean_ctor_set(x_563, 0, x_562);
lean_ctor_set(x_563, 1, x_557);
x_387 = x_563;
goto block_437;
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; 
x_564 = lean_ctor_get(x_555, 1);
lean_inc(x_564);
if (lean_is_exclusive(x_555)) {
 lean_ctor_release(x_555, 0);
 lean_ctor_release(x_555, 1);
 x_565 = x_555;
} else {
 lean_dec_ref(x_555);
 x_565 = lean_box(0);
}
x_566 = lean_ctor_get(x_556, 0);
lean_inc(x_566);
x_567 = lean_ctor_get(x_556, 1);
lean_inc(x_567);
if (lean_is_exclusive(x_556)) {
 lean_ctor_release(x_556, 0);
 lean_ctor_release(x_556, 1);
 x_568 = x_556;
} else {
 lean_dec_ref(x_556);
 x_568 = lean_box(0);
}
if (lean_is_scalar(x_568)) {
 x_569 = lean_alloc_ctor(1, 2, 0);
} else {
 x_569 = x_568;
}
lean_ctor_set(x_569, 0, x_566);
lean_ctor_set(x_569, 1, x_567);
if (lean_is_scalar(x_565)) {
 x_570 = lean_alloc_ctor(0, 2, 0);
} else {
 x_570 = x_565;
}
lean_ctor_set(x_570, 0, x_569);
lean_ctor_set(x_570, 1, x_564);
x_387 = x_570;
goto block_437;
}
}
else
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; 
x_571 = lean_ctor_get(x_555, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_555, 1);
lean_inc(x_572);
if (lean_is_exclusive(x_555)) {
 lean_ctor_release(x_555, 0);
 lean_ctor_release(x_555, 1);
 x_573 = x_555;
} else {
 lean_dec_ref(x_555);
 x_573 = lean_box(0);
}
if (lean_is_scalar(x_573)) {
 x_574 = lean_alloc_ctor(1, 2, 0);
} else {
 x_574 = x_573;
}
lean_ctor_set(x_574, 0, x_571);
lean_ctor_set(x_574, 1, x_572);
x_387 = x_574;
goto block_437;
}
}
}
}
}
else
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; 
x_585 = lean_ctor_get(x_539, 1);
lean_inc(x_585);
if (lean_is_exclusive(x_539)) {
 lean_ctor_release(x_539, 0);
 lean_ctor_release(x_539, 1);
 x_586 = x_539;
} else {
 lean_dec_ref(x_539);
 x_586 = lean_box(0);
}
x_587 = lean_ctor_get(x_540, 0);
lean_inc(x_587);
x_588 = lean_ctor_get(x_540, 1);
lean_inc(x_588);
if (lean_is_exclusive(x_540)) {
 lean_ctor_release(x_540, 0);
 lean_ctor_release(x_540, 1);
 x_589 = x_540;
} else {
 lean_dec_ref(x_540);
 x_589 = lean_box(0);
}
if (lean_is_scalar(x_589)) {
 x_590 = lean_alloc_ctor(1, 2, 0);
} else {
 x_590 = x_589;
}
lean_ctor_set(x_590, 0, x_587);
lean_ctor_set(x_590, 1, x_588);
if (lean_is_scalar(x_586)) {
 x_591 = lean_alloc_ctor(0, 2, 0);
} else {
 x_591 = x_586;
}
lean_ctor_set(x_591, 0, x_590);
lean_ctor_set(x_591, 1, x_585);
x_387 = x_591;
goto block_437;
}
}
else
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; 
x_592 = lean_ctor_get(x_539, 0);
lean_inc(x_592);
x_593 = lean_ctor_get(x_539, 1);
lean_inc(x_593);
if (lean_is_exclusive(x_539)) {
 lean_ctor_release(x_539, 0);
 lean_ctor_release(x_539, 1);
 x_594 = x_539;
} else {
 lean_dec_ref(x_539);
 x_594 = lean_box(0);
}
if (lean_is_scalar(x_594)) {
 x_595 = lean_alloc_ctor(1, 2, 0);
} else {
 x_595 = x_594;
}
lean_ctor_set(x_595, 0, x_592);
lean_ctor_set(x_595, 1, x_593);
x_387 = x_595;
goto block_437;
}
}
}
}
else
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; 
x_596 = lean_ctor_get(x_438, 0);
lean_inc(x_596);
x_597 = lean_ctor_get(x_438, 1);
lean_inc(x_597);
if (lean_is_exclusive(x_438)) {
 lean_ctor_release(x_438, 0);
 lean_ctor_release(x_438, 1);
 x_598 = x_438;
} else {
 lean_dec_ref(x_438);
 x_598 = lean_box(0);
}
if (lean_is_scalar(x_598)) {
 x_599 = lean_alloc_ctor(1, 2, 0);
} else {
 x_599 = x_598;
}
lean_ctor_set(x_599, 0, x_596);
lean_ctor_set(x_599, 1, x_597);
x_600 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_600, 0, x_599);
lean_ctor_set(x_600, 1, x_439);
x_387 = x_600;
goto block_437;
}
}
block_633:
{
if (lean_obj_tag(x_602) == 0)
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; uint8_t x_615; 
x_604 = lean_ctor_get(x_602, 0);
lean_inc(x_604);
x_605 = lean_ctor_get(x_602, 1);
lean_inc(x_605);
if (lean_is_exclusive(x_602)) {
 lean_ctor_release(x_602, 0);
 lean_ctor_release(x_602, 1);
 x_606 = x_602;
} else {
 lean_dec_ref(x_602);
 x_606 = lean_box(0);
}
x_607 = l_Lean_NameSet_empty;
x_608 = lean_box(0);
x_609 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_607, x_5, x_608);
x_610 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
x_611 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_611, 0, x_609);
lean_ctor_set(x_611, 1, x_610);
x_612 = lean_ctor_get(x_604, 1);
lean_inc(x_612);
lean_dec(x_604);
x_613 = lean_array_get_size(x_612);
x_614 = lean_unsigned_to_nat(0u);
x_615 = lean_nat_dec_lt(x_614, x_613);
if (x_615 == 0)
{
lean_object* x_616; 
lean_dec(x_613);
lean_dec(x_612);
lean_dec(x_6);
if (lean_is_scalar(x_606)) {
 x_616 = lean_alloc_ctor(0, 2, 0);
} else {
 x_616 = x_606;
}
lean_ctor_set(x_616, 0, x_611);
lean_ctor_set(x_616, 1, x_605);
x_438 = x_616;
x_439 = x_603;
goto block_601;
}
else
{
uint8_t x_617; 
x_617 = lean_nat_dec_le(x_613, x_613);
if (x_617 == 0)
{
lean_object* x_618; 
lean_dec(x_613);
lean_dec(x_612);
lean_dec(x_6);
if (lean_is_scalar(x_606)) {
 x_618 = lean_alloc_ctor(0, 2, 0);
} else {
 x_618 = x_606;
}
lean_ctor_set(x_618, 0, x_611);
lean_ctor_set(x_618, 1, x_605);
x_438 = x_618;
x_439 = x_603;
goto block_601;
}
else
{
size_t x_619; size_t x_620; lean_object* x_621; 
lean_dec(x_606);
x_619 = 0;
x_620 = lean_usize_of_nat(x_613);
lean_dec(x_613);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_621 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__7(x_6, x_612, x_619, x_620, x_611, x_8, x_9, x_10, x_11, x_605, x_603);
lean_dec(x_612);
if (lean_obj_tag(x_621) == 0)
{
lean_object* x_622; lean_object* x_623; 
x_622 = lean_ctor_get(x_621, 0);
lean_inc(x_622);
x_623 = lean_ctor_get(x_621, 1);
lean_inc(x_623);
lean_dec(x_621);
x_438 = x_622;
x_439 = x_623;
goto block_601;
}
else
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; 
x_624 = lean_ctor_get(x_621, 0);
lean_inc(x_624);
x_625 = lean_ctor_get(x_621, 1);
lean_inc(x_625);
if (lean_is_exclusive(x_621)) {
 lean_ctor_release(x_621, 0);
 lean_ctor_release(x_621, 1);
 x_626 = x_621;
} else {
 lean_dec_ref(x_621);
 x_626 = lean_box(0);
}
if (lean_is_scalar(x_626)) {
 x_627 = lean_alloc_ctor(1, 2, 0);
} else {
 x_627 = x_626;
}
lean_ctor_set(x_627, 0, x_624);
lean_ctor_set(x_627, 1, x_625);
x_387 = x_627;
goto block_437;
}
}
}
}
else
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; 
lean_dec(x_6);
lean_dec(x_5);
x_628 = lean_ctor_get(x_602, 0);
lean_inc(x_628);
x_629 = lean_ctor_get(x_602, 1);
lean_inc(x_629);
if (lean_is_exclusive(x_602)) {
 lean_ctor_release(x_602, 0);
 lean_ctor_release(x_602, 1);
 x_630 = x_602;
} else {
 lean_dec_ref(x_602);
 x_630 = lean_box(0);
}
if (lean_is_scalar(x_630)) {
 x_631 = lean_alloc_ctor(1, 2, 0);
} else {
 x_631 = x_630;
}
lean_ctor_set(x_631, 0, x_628);
lean_ctor_set(x_631, 1, x_629);
x_632 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_632, 0, x_631);
lean_ctor_set(x_632, 1, x_603);
x_387 = x_632;
goto block_437;
}
}
}
}
else
{
uint8_t x_652; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_652 = !lean_is_exclusive(x_19);
if (x_652 == 0)
{
lean_object* x_653; 
x_653 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_653, 0, x_19);
lean_ctor_set(x_653, 1, x_20);
return x_653;
}
else
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; 
x_654 = lean_ctor_get(x_19, 0);
x_655 = lean_ctor_get(x_19, 1);
lean_inc(x_655);
lean_inc(x_654);
lean_dec(x_19);
x_656 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_656, 0, x_654);
lean_ctor_set(x_656, 1, x_655);
x_657 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_657, 0, x_656);
lean_ctor_set(x_657, 1, x_20);
return x_657;
}
}
}
block_712:
{
if (lean_obj_tag(x_659) == 0)
{
uint8_t x_661; 
x_661 = !lean_is_exclusive(x_659);
if (x_661 == 0)
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; uint8_t x_672; 
x_662 = lean_ctor_get(x_659, 0);
x_663 = lean_ctor_get(x_659, 1);
x_664 = lean_ctor_get(x_2, 3);
lean_inc(x_664);
x_665 = lean_ctor_get(x_664, 1);
lean_inc(x_665);
lean_dec(x_664);
x_666 = lean_ctor_get(x_665, 6);
lean_inc(x_666);
lean_dec(x_665);
x_667 = lean_ctor_get(x_1, 0);
lean_inc(x_667);
x_668 = lean_ctor_get(x_667, 6);
lean_inc(x_668);
lean_dec(x_667);
x_669 = l_Array_append___rarg(x_666, x_668);
lean_dec(x_668);
x_670 = lean_array_get_size(x_669);
x_671 = lean_unsigned_to_nat(0u);
x_672 = lean_nat_dec_lt(x_671, x_670);
if (x_672 == 0)
{
lean_dec(x_670);
lean_dec(x_669);
x_19 = x_659;
x_20 = x_660;
goto block_658;
}
else
{
uint8_t x_673; 
x_673 = lean_nat_dec_le(x_670, x_670);
if (x_673 == 0)
{
lean_dec(x_670);
lean_dec(x_669);
x_19 = x_659;
x_20 = x_660;
goto block_658;
}
else
{
size_t x_674; size_t x_675; lean_object* x_676; 
lean_free_object(x_659);
x_674 = 0;
x_675 = lean_usize_of_nat(x_670);
lean_dec(x_670);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_676 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__13(x_2, x_669, x_674, x_675, x_662, x_8, x_9, x_10, x_11, x_663, x_660);
lean_dec(x_669);
if (lean_obj_tag(x_676) == 0)
{
lean_object* x_677; lean_object* x_678; 
x_677 = lean_ctor_get(x_676, 0);
lean_inc(x_677);
x_678 = lean_ctor_get(x_676, 1);
lean_inc(x_678);
lean_dec(x_676);
x_19 = x_677;
x_20 = x_678;
goto block_658;
}
else
{
uint8_t x_679; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_679 = !lean_is_exclusive(x_676);
if (x_679 == 0)
{
return x_676;
}
else
{
lean_object* x_680; lean_object* x_681; lean_object* x_682; 
x_680 = lean_ctor_get(x_676, 0);
x_681 = lean_ctor_get(x_676, 1);
lean_inc(x_681);
lean_inc(x_680);
lean_dec(x_676);
x_682 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_682, 0, x_680);
lean_ctor_set(x_682, 1, x_681);
return x_682;
}
}
}
}
}
else
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; uint8_t x_693; 
x_683 = lean_ctor_get(x_659, 0);
x_684 = lean_ctor_get(x_659, 1);
lean_inc(x_684);
lean_inc(x_683);
lean_dec(x_659);
x_685 = lean_ctor_get(x_2, 3);
lean_inc(x_685);
x_686 = lean_ctor_get(x_685, 1);
lean_inc(x_686);
lean_dec(x_685);
x_687 = lean_ctor_get(x_686, 6);
lean_inc(x_687);
lean_dec(x_686);
x_688 = lean_ctor_get(x_1, 0);
lean_inc(x_688);
x_689 = lean_ctor_get(x_688, 6);
lean_inc(x_689);
lean_dec(x_688);
x_690 = l_Array_append___rarg(x_687, x_689);
lean_dec(x_689);
x_691 = lean_array_get_size(x_690);
x_692 = lean_unsigned_to_nat(0u);
x_693 = lean_nat_dec_lt(x_692, x_691);
if (x_693 == 0)
{
lean_object* x_694; 
lean_dec(x_691);
lean_dec(x_690);
x_694 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_694, 0, x_683);
lean_ctor_set(x_694, 1, x_684);
x_19 = x_694;
x_20 = x_660;
goto block_658;
}
else
{
uint8_t x_695; 
x_695 = lean_nat_dec_le(x_691, x_691);
if (x_695 == 0)
{
lean_object* x_696; 
lean_dec(x_691);
lean_dec(x_690);
x_696 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_696, 0, x_683);
lean_ctor_set(x_696, 1, x_684);
x_19 = x_696;
x_20 = x_660;
goto block_658;
}
else
{
size_t x_697; size_t x_698; lean_object* x_699; 
x_697 = 0;
x_698 = lean_usize_of_nat(x_691);
lean_dec(x_691);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_699 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__13(x_2, x_690, x_697, x_698, x_683, x_8, x_9, x_10, x_11, x_684, x_660);
lean_dec(x_690);
if (lean_obj_tag(x_699) == 0)
{
lean_object* x_700; lean_object* x_701; 
x_700 = lean_ctor_get(x_699, 0);
lean_inc(x_700);
x_701 = lean_ctor_get(x_699, 1);
lean_inc(x_701);
lean_dec(x_699);
x_19 = x_700;
x_20 = x_701;
goto block_658;
}
else
{
lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_702 = lean_ctor_get(x_699, 0);
lean_inc(x_702);
x_703 = lean_ctor_get(x_699, 1);
lean_inc(x_703);
if (lean_is_exclusive(x_699)) {
 lean_ctor_release(x_699, 0);
 lean_ctor_release(x_699, 1);
 x_704 = x_699;
} else {
 lean_dec_ref(x_699);
 x_704 = lean_box(0);
}
if (lean_is_scalar(x_704)) {
 x_705 = lean_alloc_ctor(1, 2, 0);
} else {
 x_705 = x_704;
}
lean_ctor_set(x_705, 0, x_702);
lean_ctor_set(x_705, 1, x_703);
return x_705;
}
}
}
}
}
else
{
uint8_t x_706; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_706 = !lean_is_exclusive(x_659);
if (x_706 == 0)
{
lean_object* x_707; 
x_707 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_707, 0, x_659);
lean_ctor_set(x_707, 1, x_660);
return x_707;
}
else
{
lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; 
x_708 = lean_ctor_get(x_659, 0);
x_709 = lean_ctor_get(x_659, 1);
lean_inc(x_709);
lean_inc(x_708);
lean_dec(x_659);
x_710 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_710, 0, x_708);
lean_ctor_set(x_710, 1, x_709);
x_711 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_711, 0, x_710);
lean_ctor_set(x_711, 1, x_660);
return x_711;
}
}
}
}
else
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_1007; lean_object* x_1008; lean_object* x_1039; lean_object* x_1040; uint8_t x_1041; 
x_729 = lean_ctor_get(x_14, 0);
x_730 = lean_ctor_get(x_14, 1);
lean_inc(x_730);
lean_inc(x_729);
lean_dec(x_14);
x_1039 = lean_array_get_size(x_729);
x_1040 = lean_unsigned_to_nat(0u);
x_1041 = lean_nat_dec_lt(x_1040, x_1039);
if (x_1041 == 0)
{
lean_object* x_1042; lean_object* x_1043; 
lean_dec(x_1039);
x_1042 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2;
x_1043 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1043, 0, x_1042);
lean_ctor_set(x_1043, 1, x_730);
x_1007 = x_1043;
x_1008 = x_15;
goto block_1038;
}
else
{
uint8_t x_1044; 
x_1044 = lean_nat_dec_le(x_1039, x_1039);
if (x_1044 == 0)
{
lean_object* x_1045; lean_object* x_1046; 
lean_dec(x_1039);
x_1045 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2;
x_1046 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1046, 0, x_1045);
lean_ctor_set(x_1046, 1, x_730);
x_1007 = x_1046;
x_1008 = x_15;
goto block_1038;
}
else
{
size_t x_1047; size_t x_1048; lean_object* x_1049; lean_object* x_1050; 
x_1047 = 0;
x_1048 = lean_usize_of_nat(x_1039);
lean_dec(x_1039);
x_1049 = l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_1050 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__15(x_729, x_1047, x_1048, x_1049, x_8, x_9, x_10, x_11, x_730, x_15);
if (lean_obj_tag(x_1050) == 0)
{
lean_object* x_1051; lean_object* x_1052; 
x_1051 = lean_ctor_get(x_1050, 0);
lean_inc(x_1051);
x_1052 = lean_ctor_get(x_1050, 1);
lean_inc(x_1052);
lean_dec(x_1050);
x_1007 = x_1051;
x_1008 = x_1052;
goto block_1038;
}
else
{
lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; 
lean_dec(x_729);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_1053 = lean_ctor_get(x_1050, 0);
lean_inc(x_1053);
x_1054 = lean_ctor_get(x_1050, 1);
lean_inc(x_1054);
if (lean_is_exclusive(x_1050)) {
 lean_ctor_release(x_1050, 0);
 lean_ctor_release(x_1050, 1);
 x_1055 = x_1050;
} else {
 lean_dec_ref(x_1050);
 x_1055 = lean_box(0);
}
if (lean_is_scalar(x_1055)) {
 x_1056 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1056 = x_1055;
}
lean_ctor_set(x_1056, 0, x_1053);
lean_ctor_set(x_1056, 1, x_1054);
return x_1056;
}
}
}
block_1006:
{
if (lean_obj_tag(x_731) == 0)
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_787; lean_object* x_788; lean_object* x_951; lean_object* x_952; lean_object* x_983; lean_object* x_984; uint8_t x_985; 
x_733 = lean_ctor_get(x_731, 0);
lean_inc(x_733);
x_734 = lean_ctor_get(x_731, 1);
lean_inc(x_734);
if (lean_is_exclusive(x_731)) {
 lean_ctor_release(x_731, 0);
 lean_ctor_release(x_731, 1);
 x_735 = x_731;
} else {
 lean_dec_ref(x_731);
 x_735 = lean_box(0);
}
x_983 = lean_array_get_size(x_729);
x_984 = lean_unsigned_to_nat(0u);
x_985 = lean_nat_dec_lt(x_984, x_983);
if (x_985 == 0)
{
lean_object* x_986; lean_object* x_987; 
lean_dec(x_983);
lean_dec(x_729);
x_986 = l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
if (lean_is_scalar(x_735)) {
 x_987 = lean_alloc_ctor(0, 2, 0);
} else {
 x_987 = x_735;
}
lean_ctor_set(x_987, 0, x_986);
lean_ctor_set(x_987, 1, x_734);
x_951 = x_987;
x_952 = x_732;
goto block_982;
}
else
{
uint8_t x_988; 
x_988 = lean_nat_dec_le(x_983, x_983);
if (x_988 == 0)
{
lean_object* x_989; lean_object* x_990; 
lean_dec(x_983);
lean_dec(x_729);
x_989 = l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
if (lean_is_scalar(x_735)) {
 x_990 = lean_alloc_ctor(0, 2, 0);
} else {
 x_990 = x_735;
}
lean_ctor_set(x_990, 0, x_989);
lean_ctor_set(x_990, 1, x_734);
x_951 = x_990;
x_952 = x_732;
goto block_982;
}
else
{
size_t x_991; size_t x_992; lean_object* x_993; lean_object* x_994; 
lean_dec(x_735);
x_991 = 0;
x_992 = lean_usize_of_nat(x_983);
lean_dec(x_983);
x_993 = l_Lake_OrdHashSet_empty___at_Lake_OrdModuleSet_empty___spec__1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_994 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__11(x_729, x_991, x_992, x_993, x_8, x_9, x_10, x_11, x_734, x_732);
lean_dec(x_729);
if (lean_obj_tag(x_994) == 0)
{
lean_object* x_995; lean_object* x_996; 
x_995 = lean_ctor_get(x_994, 0);
lean_inc(x_995);
x_996 = lean_ctor_get(x_994, 1);
lean_inc(x_996);
lean_dec(x_994);
x_951 = x_995;
x_952 = x_996;
goto block_982;
}
else
{
lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; 
lean_dec(x_6);
lean_dec(x_5);
x_997 = lean_ctor_get(x_994, 0);
lean_inc(x_997);
x_998 = lean_ctor_get(x_994, 1);
lean_inc(x_998);
if (lean_is_exclusive(x_994)) {
 lean_ctor_release(x_994, 0);
 lean_ctor_release(x_994, 1);
 x_999 = x_994;
} else {
 lean_dec_ref(x_994);
 x_999 = lean_box(0);
}
if (lean_is_scalar(x_999)) {
 x_1000 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1000 = x_999;
}
lean_ctor_set(x_1000, 0, x_997);
lean_ctor_set(x_1000, 1, x_998);
x_736 = x_1000;
goto block_786;
}
}
}
block_786:
{
if (lean_obj_tag(x_736) == 0)
{
lean_object* x_737; 
x_737 = lean_ctor_get(x_736, 0);
lean_inc(x_737);
if (lean_obj_tag(x_737) == 0)
{
lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; uint8_t x_762; uint8_t x_763; lean_object* x_764; lean_object* x_765; 
x_738 = lean_ctor_get(x_736, 1);
lean_inc(x_738);
lean_dec(x_736);
x_739 = lean_ctor_get(x_737, 0);
lean_inc(x_739);
x_740 = lean_ctor_get(x_737, 1);
lean_inc(x_740);
if (lean_is_exclusive(x_737)) {
 lean_ctor_release(x_737, 0);
 lean_ctor_release(x_737, 1);
 x_741 = x_737;
} else {
 lean_dec_ref(x_737);
 x_741 = lean_box(0);
}
x_742 = lean_ctor_get(x_1, 4);
lean_inc(x_742);
x_743 = lean_ctor_get(x_2, 1);
lean_inc(x_743);
x_744 = lean_ctor_get(x_2, 3);
lean_inc(x_744);
lean_dec(x_2);
x_745 = lean_ctor_get(x_744, 6);
lean_inc(x_745);
x_746 = l_Lake_joinRelative(x_743, x_745);
lean_dec(x_745);
x_747 = lean_ctor_get(x_744, 8);
lean_inc(x_747);
x_748 = l_Lake_joinRelative(x_746, x_747);
lean_dec(x_747);
x_749 = l_Lake_nameToSharedLib(x_742);
x_750 = l_Lake_joinRelative(x_748, x_749);
lean_dec(x_749);
x_751 = lean_ctor_get(x_744, 1);
lean_inc(x_751);
lean_dec(x_744);
x_752 = lean_ctor_get(x_751, 9);
lean_inc(x_752);
x_753 = lean_ctor_get(x_1, 0);
lean_inc(x_753);
x_754 = lean_ctor_get(x_753, 9);
lean_inc(x_754);
x_755 = l_Array_append___rarg(x_752, x_754);
lean_dec(x_754);
x_756 = lean_ctor_get(x_751, 8);
lean_inc(x_756);
lean_dec(x_751);
x_757 = lean_ctor_get(x_753, 8);
lean_inc(x_757);
lean_dec(x_753);
x_758 = l_Array_append___rarg(x_756, x_757);
lean_dec(x_757);
x_759 = lean_ctor_get(x_1, 2);
lean_inc(x_759);
lean_dec(x_1);
x_760 = lean_array_get_size(x_759);
lean_dec(x_759);
x_761 = lean_unsigned_to_nat(1u);
x_762 = lean_nat_dec_eq(x_760, x_761);
lean_dec(x_760);
x_763 = l_System_Platform_isWindows;
x_764 = l_Lake_BuildTrace_nil;
x_765 = l_Lake_buildLeanSharedLib(x_742, x_750, x_733, x_739, x_755, x_758, x_762, x_763, x_8, x_9, x_10, x_11, x_764, x_738);
lean_dec(x_733);
if (lean_obj_tag(x_765) == 0)
{
lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; 
x_766 = lean_ctor_get(x_765, 0);
lean_inc(x_766);
x_767 = lean_ctor_get(x_765, 1);
lean_inc(x_767);
if (lean_is_exclusive(x_765)) {
 lean_ctor_release(x_765, 0);
 lean_ctor_release(x_765, 1);
 x_768 = x_765;
} else {
 lean_dec_ref(x_765);
 x_768 = lean_box(0);
}
if (lean_is_scalar(x_741)) {
 x_769 = lean_alloc_ctor(0, 2, 0);
} else {
 x_769 = x_741;
}
lean_ctor_set(x_769, 0, x_766);
lean_ctor_set(x_769, 1, x_740);
if (lean_is_scalar(x_768)) {
 x_770 = lean_alloc_ctor(0, 2, 0);
} else {
 x_770 = x_768;
}
lean_ctor_set(x_770, 0, x_769);
lean_ctor_set(x_770, 1, x_767);
return x_770;
}
else
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; 
lean_dec(x_741);
lean_dec(x_740);
x_771 = lean_ctor_get(x_765, 0);
lean_inc(x_771);
x_772 = lean_ctor_get(x_765, 1);
lean_inc(x_772);
if (lean_is_exclusive(x_765)) {
 lean_ctor_release(x_765, 0);
 lean_ctor_release(x_765, 1);
 x_773 = x_765;
} else {
 lean_dec_ref(x_765);
 x_773 = lean_box(0);
}
if (lean_is_scalar(x_773)) {
 x_774 = lean_alloc_ctor(1, 2, 0);
} else {
 x_774 = x_773;
}
lean_ctor_set(x_774, 0, x_771);
lean_ctor_set(x_774, 1, x_772);
return x_774;
}
}
else
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; 
lean_dec(x_733);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_775 = lean_ctor_get(x_736, 1);
lean_inc(x_775);
if (lean_is_exclusive(x_736)) {
 lean_ctor_release(x_736, 0);
 lean_ctor_release(x_736, 1);
 x_776 = x_736;
} else {
 lean_dec_ref(x_736);
 x_776 = lean_box(0);
}
x_777 = lean_ctor_get(x_737, 0);
lean_inc(x_777);
x_778 = lean_ctor_get(x_737, 1);
lean_inc(x_778);
if (lean_is_exclusive(x_737)) {
 lean_ctor_release(x_737, 0);
 lean_ctor_release(x_737, 1);
 x_779 = x_737;
} else {
 lean_dec_ref(x_737);
 x_779 = lean_box(0);
}
if (lean_is_scalar(x_779)) {
 x_780 = lean_alloc_ctor(1, 2, 0);
} else {
 x_780 = x_779;
}
lean_ctor_set(x_780, 0, x_777);
lean_ctor_set(x_780, 1, x_778);
if (lean_is_scalar(x_776)) {
 x_781 = lean_alloc_ctor(0, 2, 0);
} else {
 x_781 = x_776;
}
lean_ctor_set(x_781, 0, x_780);
lean_ctor_set(x_781, 1, x_775);
return x_781;
}
}
else
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; 
lean_dec(x_733);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_782 = lean_ctor_get(x_736, 0);
lean_inc(x_782);
x_783 = lean_ctor_get(x_736, 1);
lean_inc(x_783);
if (lean_is_exclusive(x_736)) {
 lean_ctor_release(x_736, 0);
 lean_ctor_release(x_736, 1);
 x_784 = x_736;
} else {
 lean_dec_ref(x_736);
 x_784 = lean_box(0);
}
if (lean_is_scalar(x_784)) {
 x_785 = lean_alloc_ctor(1, 2, 0);
} else {
 x_785 = x_784;
}
lean_ctor_set(x_785, 0, x_782);
lean_ctor_set(x_785, 1, x_783);
return x_785;
}
}
block_950:
{
if (lean_obj_tag(x_787) == 0)
{
lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; uint8_t x_802; 
x_789 = lean_ctor_get(x_787, 0);
lean_inc(x_789);
x_790 = lean_ctor_get(x_787, 1);
lean_inc(x_790);
if (lean_is_exclusive(x_787)) {
 lean_ctor_release(x_787, 0);
 lean_ctor_release(x_787, 1);
 x_791 = x_787;
} else {
 lean_dec_ref(x_787);
 x_791 = lean_box(0);
}
x_792 = lean_ctor_get(x_789, 1);
lean_inc(x_792);
if (lean_is_exclusive(x_789)) {
 lean_ctor_release(x_789, 0);
 lean_ctor_release(x_789, 1);
 x_793 = x_789;
} else {
 lean_dec_ref(x_789);
 x_793 = lean_box(0);
}
x_794 = lean_ctor_get(x_2, 3);
lean_inc(x_794);
x_795 = lean_ctor_get(x_794, 1);
lean_inc(x_795);
lean_dec(x_794);
x_796 = lean_ctor_get(x_795, 7);
lean_inc(x_796);
lean_dec(x_795);
x_797 = lean_ctor_get(x_1, 0);
lean_inc(x_797);
x_798 = lean_ctor_get(x_797, 7);
lean_inc(x_798);
lean_dec(x_797);
x_799 = l_Array_append___rarg(x_796, x_798);
lean_dec(x_798);
x_800 = lean_array_get_size(x_799);
x_801 = lean_unsigned_to_nat(0u);
x_802 = lean_nat_dec_lt(x_801, x_800);
if (x_802 == 0)
{
lean_object* x_803; lean_object* x_834; lean_object* x_835; uint8_t x_836; 
lean_dec(x_800);
lean_dec(x_799);
x_834 = lean_ctor_get(x_2, 10);
lean_inc(x_834);
x_835 = lean_array_get_size(x_834);
x_836 = lean_nat_dec_lt(x_801, x_835);
if (x_836 == 0)
{
lean_object* x_837; 
lean_dec(x_835);
lean_dec(x_834);
x_837 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
x_803 = x_837;
goto block_833;
}
else
{
uint8_t x_838; 
x_838 = lean_nat_dec_le(x_835, x_835);
if (x_838 == 0)
{
lean_object* x_839; 
lean_dec(x_835);
lean_dec(x_834);
x_839 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
x_803 = x_839;
goto block_833;
}
else
{
size_t x_840; size_t x_841; lean_object* x_842; lean_object* x_843; 
x_840 = 0;
x_841 = lean_usize_of_nat(x_835);
lean_dec(x_835);
x_842 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
lean_inc(x_2);
x_843 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__3(x_3, x_2, x_4, x_834, x_840, x_841, x_842);
lean_dec(x_834);
x_803 = x_843;
goto block_833;
}
}
block_833:
{
lean_object* x_804; uint8_t x_805; 
x_804 = lean_array_get_size(x_803);
x_805 = lean_nat_dec_lt(x_801, x_804);
if (x_805 == 0)
{
lean_object* x_806; lean_object* x_807; 
lean_dec(x_804);
lean_dec(x_803);
if (lean_is_scalar(x_791)) {
 x_806 = lean_alloc_ctor(0, 2, 0);
} else {
 x_806 = x_791;
}
lean_ctor_set(x_806, 0, x_792);
lean_ctor_set(x_806, 1, x_790);
if (lean_is_scalar(x_793)) {
 x_807 = lean_alloc_ctor(0, 2, 0);
} else {
 x_807 = x_793;
}
lean_ctor_set(x_807, 0, x_806);
lean_ctor_set(x_807, 1, x_788);
x_736 = x_807;
goto block_786;
}
else
{
uint8_t x_808; 
x_808 = lean_nat_dec_le(x_804, x_804);
if (x_808 == 0)
{
lean_object* x_809; lean_object* x_810; 
lean_dec(x_804);
lean_dec(x_803);
if (lean_is_scalar(x_791)) {
 x_809 = lean_alloc_ctor(0, 2, 0);
} else {
 x_809 = x_791;
}
lean_ctor_set(x_809, 0, x_792);
lean_ctor_set(x_809, 1, x_790);
if (lean_is_scalar(x_793)) {
 x_810 = lean_alloc_ctor(0, 2, 0);
} else {
 x_810 = x_793;
}
lean_ctor_set(x_810, 0, x_809);
lean_ctor_set(x_810, 1, x_788);
x_736 = x_810;
goto block_786;
}
else
{
size_t x_811; size_t x_812; lean_object* x_813; 
lean_dec(x_793);
lean_dec(x_791);
x_811 = 0;
x_812 = lean_usize_of_nat(x_804);
lean_dec(x_804);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_813 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__2(x_803, x_811, x_812, x_792, x_8, x_9, x_10, x_11, x_790, x_788);
lean_dec(x_803);
if (lean_obj_tag(x_813) == 0)
{
lean_object* x_814; 
x_814 = lean_ctor_get(x_813, 0);
lean_inc(x_814);
if (lean_obj_tag(x_814) == 0)
{
lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; 
x_815 = lean_ctor_get(x_813, 1);
lean_inc(x_815);
if (lean_is_exclusive(x_813)) {
 lean_ctor_release(x_813, 0);
 lean_ctor_release(x_813, 1);
 x_816 = x_813;
} else {
 lean_dec_ref(x_813);
 x_816 = lean_box(0);
}
x_817 = lean_ctor_get(x_814, 0);
lean_inc(x_817);
x_818 = lean_ctor_get(x_814, 1);
lean_inc(x_818);
if (lean_is_exclusive(x_814)) {
 lean_ctor_release(x_814, 0);
 lean_ctor_release(x_814, 1);
 x_819 = x_814;
} else {
 lean_dec_ref(x_814);
 x_819 = lean_box(0);
}
if (lean_is_scalar(x_819)) {
 x_820 = lean_alloc_ctor(0, 2, 0);
} else {
 x_820 = x_819;
}
lean_ctor_set(x_820, 0, x_817);
lean_ctor_set(x_820, 1, x_818);
if (lean_is_scalar(x_816)) {
 x_821 = lean_alloc_ctor(0, 2, 0);
} else {
 x_821 = x_816;
}
lean_ctor_set(x_821, 0, x_820);
lean_ctor_set(x_821, 1, x_815);
x_736 = x_821;
goto block_786;
}
else
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; 
x_822 = lean_ctor_get(x_813, 1);
lean_inc(x_822);
if (lean_is_exclusive(x_813)) {
 lean_ctor_release(x_813, 0);
 lean_ctor_release(x_813, 1);
 x_823 = x_813;
} else {
 lean_dec_ref(x_813);
 x_823 = lean_box(0);
}
x_824 = lean_ctor_get(x_814, 0);
lean_inc(x_824);
x_825 = lean_ctor_get(x_814, 1);
lean_inc(x_825);
if (lean_is_exclusive(x_814)) {
 lean_ctor_release(x_814, 0);
 lean_ctor_release(x_814, 1);
 x_826 = x_814;
} else {
 lean_dec_ref(x_814);
 x_826 = lean_box(0);
}
if (lean_is_scalar(x_826)) {
 x_827 = lean_alloc_ctor(1, 2, 0);
} else {
 x_827 = x_826;
}
lean_ctor_set(x_827, 0, x_824);
lean_ctor_set(x_827, 1, x_825);
if (lean_is_scalar(x_823)) {
 x_828 = lean_alloc_ctor(0, 2, 0);
} else {
 x_828 = x_823;
}
lean_ctor_set(x_828, 0, x_827);
lean_ctor_set(x_828, 1, x_822);
x_736 = x_828;
goto block_786;
}
}
else
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; 
x_829 = lean_ctor_get(x_813, 0);
lean_inc(x_829);
x_830 = lean_ctor_get(x_813, 1);
lean_inc(x_830);
if (lean_is_exclusive(x_813)) {
 lean_ctor_release(x_813, 0);
 lean_ctor_release(x_813, 1);
 x_831 = x_813;
} else {
 lean_dec_ref(x_813);
 x_831 = lean_box(0);
}
if (lean_is_scalar(x_831)) {
 x_832 = lean_alloc_ctor(1, 2, 0);
} else {
 x_832 = x_831;
}
lean_ctor_set(x_832, 0, x_829);
lean_ctor_set(x_832, 1, x_830);
x_736 = x_832;
goto block_786;
}
}
}
}
}
else
{
uint8_t x_844; 
x_844 = lean_nat_dec_le(x_800, x_800);
if (x_844 == 0)
{
lean_object* x_845; lean_object* x_876; lean_object* x_877; uint8_t x_878; 
lean_dec(x_800);
lean_dec(x_799);
x_876 = lean_ctor_get(x_2, 10);
lean_inc(x_876);
x_877 = lean_array_get_size(x_876);
x_878 = lean_nat_dec_lt(x_801, x_877);
if (x_878 == 0)
{
lean_object* x_879; 
lean_dec(x_877);
lean_dec(x_876);
x_879 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
x_845 = x_879;
goto block_875;
}
else
{
uint8_t x_880; 
x_880 = lean_nat_dec_le(x_877, x_877);
if (x_880 == 0)
{
lean_object* x_881; 
lean_dec(x_877);
lean_dec(x_876);
x_881 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
x_845 = x_881;
goto block_875;
}
else
{
size_t x_882; size_t x_883; lean_object* x_884; lean_object* x_885; 
x_882 = 0;
x_883 = lean_usize_of_nat(x_877);
lean_dec(x_877);
x_884 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
lean_inc(x_2);
x_885 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__4(x_3, x_2, x_4, x_876, x_882, x_883, x_884);
lean_dec(x_876);
x_845 = x_885;
goto block_875;
}
}
block_875:
{
lean_object* x_846; uint8_t x_847; 
x_846 = lean_array_get_size(x_845);
x_847 = lean_nat_dec_lt(x_801, x_846);
if (x_847 == 0)
{
lean_object* x_848; lean_object* x_849; 
lean_dec(x_846);
lean_dec(x_845);
if (lean_is_scalar(x_791)) {
 x_848 = lean_alloc_ctor(0, 2, 0);
} else {
 x_848 = x_791;
}
lean_ctor_set(x_848, 0, x_792);
lean_ctor_set(x_848, 1, x_790);
if (lean_is_scalar(x_793)) {
 x_849 = lean_alloc_ctor(0, 2, 0);
} else {
 x_849 = x_793;
}
lean_ctor_set(x_849, 0, x_848);
lean_ctor_set(x_849, 1, x_788);
x_736 = x_849;
goto block_786;
}
else
{
uint8_t x_850; 
x_850 = lean_nat_dec_le(x_846, x_846);
if (x_850 == 0)
{
lean_object* x_851; lean_object* x_852; 
lean_dec(x_846);
lean_dec(x_845);
if (lean_is_scalar(x_791)) {
 x_851 = lean_alloc_ctor(0, 2, 0);
} else {
 x_851 = x_791;
}
lean_ctor_set(x_851, 0, x_792);
lean_ctor_set(x_851, 1, x_790);
if (lean_is_scalar(x_793)) {
 x_852 = lean_alloc_ctor(0, 2, 0);
} else {
 x_852 = x_793;
}
lean_ctor_set(x_852, 0, x_851);
lean_ctor_set(x_852, 1, x_788);
x_736 = x_852;
goto block_786;
}
else
{
size_t x_853; size_t x_854; lean_object* x_855; 
lean_dec(x_793);
lean_dec(x_791);
x_853 = 0;
x_854 = lean_usize_of_nat(x_846);
lean_dec(x_846);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_855 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__2(x_845, x_853, x_854, x_792, x_8, x_9, x_10, x_11, x_790, x_788);
lean_dec(x_845);
if (lean_obj_tag(x_855) == 0)
{
lean_object* x_856; 
x_856 = lean_ctor_get(x_855, 0);
lean_inc(x_856);
if (lean_obj_tag(x_856) == 0)
{
lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; 
x_857 = lean_ctor_get(x_855, 1);
lean_inc(x_857);
if (lean_is_exclusive(x_855)) {
 lean_ctor_release(x_855, 0);
 lean_ctor_release(x_855, 1);
 x_858 = x_855;
} else {
 lean_dec_ref(x_855);
 x_858 = lean_box(0);
}
x_859 = lean_ctor_get(x_856, 0);
lean_inc(x_859);
x_860 = lean_ctor_get(x_856, 1);
lean_inc(x_860);
if (lean_is_exclusive(x_856)) {
 lean_ctor_release(x_856, 0);
 lean_ctor_release(x_856, 1);
 x_861 = x_856;
} else {
 lean_dec_ref(x_856);
 x_861 = lean_box(0);
}
if (lean_is_scalar(x_861)) {
 x_862 = lean_alloc_ctor(0, 2, 0);
} else {
 x_862 = x_861;
}
lean_ctor_set(x_862, 0, x_859);
lean_ctor_set(x_862, 1, x_860);
if (lean_is_scalar(x_858)) {
 x_863 = lean_alloc_ctor(0, 2, 0);
} else {
 x_863 = x_858;
}
lean_ctor_set(x_863, 0, x_862);
lean_ctor_set(x_863, 1, x_857);
x_736 = x_863;
goto block_786;
}
else
{
lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; 
x_864 = lean_ctor_get(x_855, 1);
lean_inc(x_864);
if (lean_is_exclusive(x_855)) {
 lean_ctor_release(x_855, 0);
 lean_ctor_release(x_855, 1);
 x_865 = x_855;
} else {
 lean_dec_ref(x_855);
 x_865 = lean_box(0);
}
x_866 = lean_ctor_get(x_856, 0);
lean_inc(x_866);
x_867 = lean_ctor_get(x_856, 1);
lean_inc(x_867);
if (lean_is_exclusive(x_856)) {
 lean_ctor_release(x_856, 0);
 lean_ctor_release(x_856, 1);
 x_868 = x_856;
} else {
 lean_dec_ref(x_856);
 x_868 = lean_box(0);
}
if (lean_is_scalar(x_868)) {
 x_869 = lean_alloc_ctor(1, 2, 0);
} else {
 x_869 = x_868;
}
lean_ctor_set(x_869, 0, x_866);
lean_ctor_set(x_869, 1, x_867);
if (lean_is_scalar(x_865)) {
 x_870 = lean_alloc_ctor(0, 2, 0);
} else {
 x_870 = x_865;
}
lean_ctor_set(x_870, 0, x_869);
lean_ctor_set(x_870, 1, x_864);
x_736 = x_870;
goto block_786;
}
}
else
{
lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; 
x_871 = lean_ctor_get(x_855, 0);
lean_inc(x_871);
x_872 = lean_ctor_get(x_855, 1);
lean_inc(x_872);
if (lean_is_exclusive(x_855)) {
 lean_ctor_release(x_855, 0);
 lean_ctor_release(x_855, 1);
 x_873 = x_855;
} else {
 lean_dec_ref(x_855);
 x_873 = lean_box(0);
}
if (lean_is_scalar(x_873)) {
 x_874 = lean_alloc_ctor(1, 2, 0);
} else {
 x_874 = x_873;
}
lean_ctor_set(x_874, 0, x_871);
lean_ctor_set(x_874, 1, x_872);
x_736 = x_874;
goto block_786;
}
}
}
}
}
else
{
size_t x_886; size_t x_887; lean_object* x_888; 
lean_dec(x_793);
lean_dec(x_791);
x_886 = 0;
x_887 = lean_usize_of_nat(x_800);
lean_dec(x_800);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_888 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__5(x_2, x_799, x_886, x_887, x_792, x_8, x_9, x_10, x_11, x_790, x_788);
lean_dec(x_799);
if (lean_obj_tag(x_888) == 0)
{
lean_object* x_889; 
x_889 = lean_ctor_get(x_888, 0);
lean_inc(x_889);
if (lean_obj_tag(x_889) == 0)
{
lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_925; lean_object* x_926; uint8_t x_927; 
x_890 = lean_ctor_get(x_888, 1);
lean_inc(x_890);
if (lean_is_exclusive(x_888)) {
 lean_ctor_release(x_888, 0);
 lean_ctor_release(x_888, 1);
 x_891 = x_888;
} else {
 lean_dec_ref(x_888);
 x_891 = lean_box(0);
}
x_892 = lean_ctor_get(x_889, 0);
lean_inc(x_892);
x_893 = lean_ctor_get(x_889, 1);
lean_inc(x_893);
if (lean_is_exclusive(x_889)) {
 lean_ctor_release(x_889, 0);
 lean_ctor_release(x_889, 1);
 x_894 = x_889;
} else {
 lean_dec_ref(x_889);
 x_894 = lean_box(0);
}
x_925 = lean_ctor_get(x_2, 10);
lean_inc(x_925);
x_926 = lean_array_get_size(x_925);
x_927 = lean_nat_dec_lt(x_801, x_926);
if (x_927 == 0)
{
lean_object* x_928; 
lean_dec(x_926);
lean_dec(x_925);
x_928 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
x_895 = x_928;
goto block_924;
}
else
{
uint8_t x_929; 
x_929 = lean_nat_dec_le(x_926, x_926);
if (x_929 == 0)
{
lean_object* x_930; 
lean_dec(x_926);
lean_dec(x_925);
x_930 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
x_895 = x_930;
goto block_924;
}
else
{
size_t x_931; lean_object* x_932; lean_object* x_933; 
x_931 = lean_usize_of_nat(x_926);
lean_dec(x_926);
x_932 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
lean_inc(x_2);
x_933 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__6(x_3, x_2, x_4, x_925, x_886, x_931, x_932);
lean_dec(x_925);
x_895 = x_933;
goto block_924;
}
}
block_924:
{
lean_object* x_896; uint8_t x_897; 
x_896 = lean_array_get_size(x_895);
x_897 = lean_nat_dec_lt(x_801, x_896);
if (x_897 == 0)
{
lean_object* x_898; lean_object* x_899; 
lean_dec(x_896);
lean_dec(x_895);
if (lean_is_scalar(x_894)) {
 x_898 = lean_alloc_ctor(0, 2, 0);
} else {
 x_898 = x_894;
}
lean_ctor_set(x_898, 0, x_892);
lean_ctor_set(x_898, 1, x_893);
if (lean_is_scalar(x_891)) {
 x_899 = lean_alloc_ctor(0, 2, 0);
} else {
 x_899 = x_891;
}
lean_ctor_set(x_899, 0, x_898);
lean_ctor_set(x_899, 1, x_890);
x_736 = x_899;
goto block_786;
}
else
{
uint8_t x_900; 
x_900 = lean_nat_dec_le(x_896, x_896);
if (x_900 == 0)
{
lean_object* x_901; lean_object* x_902; 
lean_dec(x_896);
lean_dec(x_895);
if (lean_is_scalar(x_894)) {
 x_901 = lean_alloc_ctor(0, 2, 0);
} else {
 x_901 = x_894;
}
lean_ctor_set(x_901, 0, x_892);
lean_ctor_set(x_901, 1, x_893);
if (lean_is_scalar(x_891)) {
 x_902 = lean_alloc_ctor(0, 2, 0);
} else {
 x_902 = x_891;
}
lean_ctor_set(x_902, 0, x_901);
lean_ctor_set(x_902, 1, x_890);
x_736 = x_902;
goto block_786;
}
else
{
size_t x_903; lean_object* x_904; 
lean_dec(x_894);
lean_dec(x_891);
x_903 = lean_usize_of_nat(x_896);
lean_dec(x_896);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_904 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__2(x_895, x_886, x_903, x_892, x_8, x_9, x_10, x_11, x_893, x_890);
lean_dec(x_895);
if (lean_obj_tag(x_904) == 0)
{
lean_object* x_905; 
x_905 = lean_ctor_get(x_904, 0);
lean_inc(x_905);
if (lean_obj_tag(x_905) == 0)
{
lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; 
x_906 = lean_ctor_get(x_904, 1);
lean_inc(x_906);
if (lean_is_exclusive(x_904)) {
 lean_ctor_release(x_904, 0);
 lean_ctor_release(x_904, 1);
 x_907 = x_904;
} else {
 lean_dec_ref(x_904);
 x_907 = lean_box(0);
}
x_908 = lean_ctor_get(x_905, 0);
lean_inc(x_908);
x_909 = lean_ctor_get(x_905, 1);
lean_inc(x_909);
if (lean_is_exclusive(x_905)) {
 lean_ctor_release(x_905, 0);
 lean_ctor_release(x_905, 1);
 x_910 = x_905;
} else {
 lean_dec_ref(x_905);
 x_910 = lean_box(0);
}
if (lean_is_scalar(x_910)) {
 x_911 = lean_alloc_ctor(0, 2, 0);
} else {
 x_911 = x_910;
}
lean_ctor_set(x_911, 0, x_908);
lean_ctor_set(x_911, 1, x_909);
if (lean_is_scalar(x_907)) {
 x_912 = lean_alloc_ctor(0, 2, 0);
} else {
 x_912 = x_907;
}
lean_ctor_set(x_912, 0, x_911);
lean_ctor_set(x_912, 1, x_906);
x_736 = x_912;
goto block_786;
}
else
{
lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; 
x_913 = lean_ctor_get(x_904, 1);
lean_inc(x_913);
if (lean_is_exclusive(x_904)) {
 lean_ctor_release(x_904, 0);
 lean_ctor_release(x_904, 1);
 x_914 = x_904;
} else {
 lean_dec_ref(x_904);
 x_914 = lean_box(0);
}
x_915 = lean_ctor_get(x_905, 0);
lean_inc(x_915);
x_916 = lean_ctor_get(x_905, 1);
lean_inc(x_916);
if (lean_is_exclusive(x_905)) {
 lean_ctor_release(x_905, 0);
 lean_ctor_release(x_905, 1);
 x_917 = x_905;
} else {
 lean_dec_ref(x_905);
 x_917 = lean_box(0);
}
if (lean_is_scalar(x_917)) {
 x_918 = lean_alloc_ctor(1, 2, 0);
} else {
 x_918 = x_917;
}
lean_ctor_set(x_918, 0, x_915);
lean_ctor_set(x_918, 1, x_916);
if (lean_is_scalar(x_914)) {
 x_919 = lean_alloc_ctor(0, 2, 0);
} else {
 x_919 = x_914;
}
lean_ctor_set(x_919, 0, x_918);
lean_ctor_set(x_919, 1, x_913);
x_736 = x_919;
goto block_786;
}
}
else
{
lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; 
x_920 = lean_ctor_get(x_904, 0);
lean_inc(x_920);
x_921 = lean_ctor_get(x_904, 1);
lean_inc(x_921);
if (lean_is_exclusive(x_904)) {
 lean_ctor_release(x_904, 0);
 lean_ctor_release(x_904, 1);
 x_922 = x_904;
} else {
 lean_dec_ref(x_904);
 x_922 = lean_box(0);
}
if (lean_is_scalar(x_922)) {
 x_923 = lean_alloc_ctor(1, 2, 0);
} else {
 x_923 = x_922;
}
lean_ctor_set(x_923, 0, x_920);
lean_ctor_set(x_923, 1, x_921);
x_736 = x_923;
goto block_786;
}
}
}
}
}
else
{
lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; 
x_934 = lean_ctor_get(x_888, 1);
lean_inc(x_934);
if (lean_is_exclusive(x_888)) {
 lean_ctor_release(x_888, 0);
 lean_ctor_release(x_888, 1);
 x_935 = x_888;
} else {
 lean_dec_ref(x_888);
 x_935 = lean_box(0);
}
x_936 = lean_ctor_get(x_889, 0);
lean_inc(x_936);
x_937 = lean_ctor_get(x_889, 1);
lean_inc(x_937);
if (lean_is_exclusive(x_889)) {
 lean_ctor_release(x_889, 0);
 lean_ctor_release(x_889, 1);
 x_938 = x_889;
} else {
 lean_dec_ref(x_889);
 x_938 = lean_box(0);
}
if (lean_is_scalar(x_938)) {
 x_939 = lean_alloc_ctor(1, 2, 0);
} else {
 x_939 = x_938;
}
lean_ctor_set(x_939, 0, x_936);
lean_ctor_set(x_939, 1, x_937);
if (lean_is_scalar(x_935)) {
 x_940 = lean_alloc_ctor(0, 2, 0);
} else {
 x_940 = x_935;
}
lean_ctor_set(x_940, 0, x_939);
lean_ctor_set(x_940, 1, x_934);
x_736 = x_940;
goto block_786;
}
}
else
{
lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; 
x_941 = lean_ctor_get(x_888, 0);
lean_inc(x_941);
x_942 = lean_ctor_get(x_888, 1);
lean_inc(x_942);
if (lean_is_exclusive(x_888)) {
 lean_ctor_release(x_888, 0);
 lean_ctor_release(x_888, 1);
 x_943 = x_888;
} else {
 lean_dec_ref(x_888);
 x_943 = lean_box(0);
}
if (lean_is_scalar(x_943)) {
 x_944 = lean_alloc_ctor(1, 2, 0);
} else {
 x_944 = x_943;
}
lean_ctor_set(x_944, 0, x_941);
lean_ctor_set(x_944, 1, x_942);
x_736 = x_944;
goto block_786;
}
}
}
}
else
{
lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; 
x_945 = lean_ctor_get(x_787, 0);
lean_inc(x_945);
x_946 = lean_ctor_get(x_787, 1);
lean_inc(x_946);
if (lean_is_exclusive(x_787)) {
 lean_ctor_release(x_787, 0);
 lean_ctor_release(x_787, 1);
 x_947 = x_787;
} else {
 lean_dec_ref(x_787);
 x_947 = lean_box(0);
}
if (lean_is_scalar(x_947)) {
 x_948 = lean_alloc_ctor(1, 2, 0);
} else {
 x_948 = x_947;
}
lean_ctor_set(x_948, 0, x_945);
lean_ctor_set(x_948, 1, x_946);
x_949 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_949, 0, x_948);
lean_ctor_set(x_949, 1, x_788);
x_736 = x_949;
goto block_786;
}
}
block_982:
{
if (lean_obj_tag(x_951) == 0)
{
lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; uint8_t x_964; 
x_953 = lean_ctor_get(x_951, 0);
lean_inc(x_953);
x_954 = lean_ctor_get(x_951, 1);
lean_inc(x_954);
if (lean_is_exclusive(x_951)) {
 lean_ctor_release(x_951, 0);
 lean_ctor_release(x_951, 1);
 x_955 = x_951;
} else {
 lean_dec_ref(x_951);
 x_955 = lean_box(0);
}
x_956 = l_Lean_NameSet_empty;
x_957 = lean_box(0);
x_958 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_956, x_5, x_957);
x_959 = l_Lake_LeanLib_recCollectLocalModules___closed__1;
x_960 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_960, 0, x_958);
lean_ctor_set(x_960, 1, x_959);
x_961 = lean_ctor_get(x_953, 1);
lean_inc(x_961);
lean_dec(x_953);
x_962 = lean_array_get_size(x_961);
x_963 = lean_unsigned_to_nat(0u);
x_964 = lean_nat_dec_lt(x_963, x_962);
if (x_964 == 0)
{
lean_object* x_965; 
lean_dec(x_962);
lean_dec(x_961);
lean_dec(x_6);
if (lean_is_scalar(x_955)) {
 x_965 = lean_alloc_ctor(0, 2, 0);
} else {
 x_965 = x_955;
}
lean_ctor_set(x_965, 0, x_960);
lean_ctor_set(x_965, 1, x_954);
x_787 = x_965;
x_788 = x_952;
goto block_950;
}
else
{
uint8_t x_966; 
x_966 = lean_nat_dec_le(x_962, x_962);
if (x_966 == 0)
{
lean_object* x_967; 
lean_dec(x_962);
lean_dec(x_961);
lean_dec(x_6);
if (lean_is_scalar(x_955)) {
 x_967 = lean_alloc_ctor(0, 2, 0);
} else {
 x_967 = x_955;
}
lean_ctor_set(x_967, 0, x_960);
lean_ctor_set(x_967, 1, x_954);
x_787 = x_967;
x_788 = x_952;
goto block_950;
}
else
{
size_t x_968; size_t x_969; lean_object* x_970; 
lean_dec(x_955);
x_968 = 0;
x_969 = lean_usize_of_nat(x_962);
lean_dec(x_962);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_970 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__7(x_6, x_961, x_968, x_969, x_960, x_8, x_9, x_10, x_11, x_954, x_952);
lean_dec(x_961);
if (lean_obj_tag(x_970) == 0)
{
lean_object* x_971; lean_object* x_972; 
x_971 = lean_ctor_get(x_970, 0);
lean_inc(x_971);
x_972 = lean_ctor_get(x_970, 1);
lean_inc(x_972);
lean_dec(x_970);
x_787 = x_971;
x_788 = x_972;
goto block_950;
}
else
{
lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; 
x_973 = lean_ctor_get(x_970, 0);
lean_inc(x_973);
x_974 = lean_ctor_get(x_970, 1);
lean_inc(x_974);
if (lean_is_exclusive(x_970)) {
 lean_ctor_release(x_970, 0);
 lean_ctor_release(x_970, 1);
 x_975 = x_970;
} else {
 lean_dec_ref(x_970);
 x_975 = lean_box(0);
}
if (lean_is_scalar(x_975)) {
 x_976 = lean_alloc_ctor(1, 2, 0);
} else {
 x_976 = x_975;
}
lean_ctor_set(x_976, 0, x_973);
lean_ctor_set(x_976, 1, x_974);
x_736 = x_976;
goto block_786;
}
}
}
}
else
{
lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; 
lean_dec(x_6);
lean_dec(x_5);
x_977 = lean_ctor_get(x_951, 0);
lean_inc(x_977);
x_978 = lean_ctor_get(x_951, 1);
lean_inc(x_978);
if (lean_is_exclusive(x_951)) {
 lean_ctor_release(x_951, 0);
 lean_ctor_release(x_951, 1);
 x_979 = x_951;
} else {
 lean_dec_ref(x_951);
 x_979 = lean_box(0);
}
if (lean_is_scalar(x_979)) {
 x_980 = lean_alloc_ctor(1, 2, 0);
} else {
 x_980 = x_979;
}
lean_ctor_set(x_980, 0, x_977);
lean_ctor_set(x_980, 1, x_978);
x_981 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_981, 0, x_980);
lean_ctor_set(x_981, 1, x_952);
x_736 = x_981;
goto block_786;
}
}
}
else
{
lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; 
lean_dec(x_729);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_1001 = lean_ctor_get(x_731, 0);
lean_inc(x_1001);
x_1002 = lean_ctor_get(x_731, 1);
lean_inc(x_1002);
if (lean_is_exclusive(x_731)) {
 lean_ctor_release(x_731, 0);
 lean_ctor_release(x_731, 1);
 x_1003 = x_731;
} else {
 lean_dec_ref(x_731);
 x_1003 = lean_box(0);
}
if (lean_is_scalar(x_1003)) {
 x_1004 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1004 = x_1003;
}
lean_ctor_set(x_1004, 0, x_1001);
lean_ctor_set(x_1004, 1, x_1002);
x_1005 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1005, 0, x_1004);
lean_ctor_set(x_1005, 1, x_732);
return x_1005;
}
}
block_1038:
{
if (lean_obj_tag(x_1007) == 0)
{
lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; uint8_t x_1020; 
x_1009 = lean_ctor_get(x_1007, 0);
lean_inc(x_1009);
x_1010 = lean_ctor_get(x_1007, 1);
lean_inc(x_1010);
if (lean_is_exclusive(x_1007)) {
 lean_ctor_release(x_1007, 0);
 lean_ctor_release(x_1007, 1);
 x_1011 = x_1007;
} else {
 lean_dec_ref(x_1007);
 x_1011 = lean_box(0);
}
x_1012 = lean_ctor_get(x_2, 3);
lean_inc(x_1012);
x_1013 = lean_ctor_get(x_1012, 1);
lean_inc(x_1013);
lean_dec(x_1012);
x_1014 = lean_ctor_get(x_1013, 6);
lean_inc(x_1014);
lean_dec(x_1013);
x_1015 = lean_ctor_get(x_1, 0);
lean_inc(x_1015);
x_1016 = lean_ctor_get(x_1015, 6);
lean_inc(x_1016);
lean_dec(x_1015);
x_1017 = l_Array_append___rarg(x_1014, x_1016);
lean_dec(x_1016);
x_1018 = lean_array_get_size(x_1017);
x_1019 = lean_unsigned_to_nat(0u);
x_1020 = lean_nat_dec_lt(x_1019, x_1018);
if (x_1020 == 0)
{
lean_object* x_1021; 
lean_dec(x_1018);
lean_dec(x_1017);
if (lean_is_scalar(x_1011)) {
 x_1021 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1021 = x_1011;
}
lean_ctor_set(x_1021, 0, x_1009);
lean_ctor_set(x_1021, 1, x_1010);
x_731 = x_1021;
x_732 = x_1008;
goto block_1006;
}
else
{
uint8_t x_1022; 
x_1022 = lean_nat_dec_le(x_1018, x_1018);
if (x_1022 == 0)
{
lean_object* x_1023; 
lean_dec(x_1018);
lean_dec(x_1017);
if (lean_is_scalar(x_1011)) {
 x_1023 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1023 = x_1011;
}
lean_ctor_set(x_1023, 0, x_1009);
lean_ctor_set(x_1023, 1, x_1010);
x_731 = x_1023;
x_732 = x_1008;
goto block_1006;
}
else
{
size_t x_1024; size_t x_1025; lean_object* x_1026; 
lean_dec(x_1011);
x_1024 = 0;
x_1025 = lean_usize_of_nat(x_1018);
lean_dec(x_1018);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_1026 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__13(x_2, x_1017, x_1024, x_1025, x_1009, x_8, x_9, x_10, x_11, x_1010, x_1008);
lean_dec(x_1017);
if (lean_obj_tag(x_1026) == 0)
{
lean_object* x_1027; lean_object* x_1028; 
x_1027 = lean_ctor_get(x_1026, 0);
lean_inc(x_1027);
x_1028 = lean_ctor_get(x_1026, 1);
lean_inc(x_1028);
lean_dec(x_1026);
x_731 = x_1027;
x_732 = x_1028;
goto block_1006;
}
else
{
lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; 
lean_dec(x_729);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_1029 = lean_ctor_get(x_1026, 0);
lean_inc(x_1029);
x_1030 = lean_ctor_get(x_1026, 1);
lean_inc(x_1030);
if (lean_is_exclusive(x_1026)) {
 lean_ctor_release(x_1026, 0);
 lean_ctor_release(x_1026, 1);
 x_1031 = x_1026;
} else {
 lean_dec_ref(x_1026);
 x_1031 = lean_box(0);
}
if (lean_is_scalar(x_1031)) {
 x_1032 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1032 = x_1031;
}
lean_ctor_set(x_1032, 0, x_1029);
lean_ctor_set(x_1032, 1, x_1030);
return x_1032;
}
}
}
}
else
{
lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; 
lean_dec(x_729);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_1033 = lean_ctor_get(x_1007, 0);
lean_inc(x_1033);
x_1034 = lean_ctor_get(x_1007, 1);
lean_inc(x_1034);
if (lean_is_exclusive(x_1007)) {
 lean_ctor_release(x_1007, 0);
 lean_ctor_release(x_1007, 1);
 x_1035 = x_1007;
} else {
 lean_dec_ref(x_1007);
 x_1035 = lean_box(0);
}
if (lean_is_scalar(x_1035)) {
 x_1036 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1036 = x_1035;
}
lean_ctor_set(x_1036, 0, x_1033);
lean_ctor_set(x_1036, 1, x_1034);
x_1037 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1037, 0, x_1036);
lean_ctor_set(x_1037, 1, x_1008);
return x_1037;
}
}
}
}
else
{
uint8_t x_1057; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_1057 = !lean_is_exclusive(x_14);
if (x_1057 == 0)
{
lean_object* x_1058; 
x_1058 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1058, 0, x_14);
lean_ctor_set(x_1058, 1, x_15);
return x_1058;
}
else
{
lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; 
x_1059 = lean_ctor_get(x_14, 0);
x_1060 = lean_ctor_get(x_14, 1);
lean_inc(x_1060);
lean_inc(x_1059);
lean_dec(x_14);
x_1061 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1061, 0, x_1059);
lean_ctor_set(x_1061, 1, x_1060);
x_1062 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1062, 0, x_1061);
lean_ctor_set(x_1062, 1, x_15);
return x_1062;
}
}
}
block_1080:
{
if (lean_obj_tag(x_1064) == 0)
{
uint8_t x_1066; 
x_1066 = !lean_is_exclusive(x_1064);
if (x_1066 == 0)
{
lean_object* x_1067; lean_object* x_1068; 
x_1067 = lean_ctor_get(x_1064, 1);
x_1068 = lean_ctor_get(x_1067, 0);
lean_inc(x_1068);
lean_dec(x_1067);
lean_ctor_set(x_1064, 1, x_1068);
x_14 = x_1064;
x_15 = x_1065;
goto block_1063;
}
else
{
lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; 
x_1069 = lean_ctor_get(x_1064, 0);
x_1070 = lean_ctor_get(x_1064, 1);
lean_inc(x_1070);
lean_inc(x_1069);
lean_dec(x_1064);
x_1071 = lean_ctor_get(x_1070, 0);
lean_inc(x_1071);
lean_dec(x_1070);
x_1072 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1072, 0, x_1069);
lean_ctor_set(x_1072, 1, x_1071);
x_14 = x_1072;
x_15 = x_1065;
goto block_1063;
}
}
else
{
uint8_t x_1073; 
x_1073 = !lean_is_exclusive(x_1064);
if (x_1073 == 0)
{
lean_object* x_1074; lean_object* x_1075; 
x_1074 = lean_ctor_get(x_1064, 1);
x_1075 = lean_ctor_get(x_1074, 0);
lean_inc(x_1075);
lean_dec(x_1074);
lean_ctor_set(x_1064, 1, x_1075);
x_14 = x_1064;
x_15 = x_1065;
goto block_1063;
}
else
{
lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; 
x_1076 = lean_ctor_get(x_1064, 0);
x_1077 = lean_ctor_get(x_1064, 1);
lean_inc(x_1077);
lean_inc(x_1076);
lean_dec(x_1064);
x_1078 = lean_ctor_get(x_1077, 0);
lean_inc(x_1078);
lean_dec(x_1077);
x_1079 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1079, 0, x_1076);
lean_ctor_set(x_1079, 1, x_1078);
x_14 = x_1079;
x_15 = x_1065;
goto block_1063;
}
}
}
block_1105:
{
if (lean_obj_tag(x_1081) == 0)
{
uint8_t x_1083; 
x_1083 = !lean_is_exclusive(x_1081);
if (x_1083 == 0)
{
lean_object* x_1084; uint8_t x_1085; lean_object* x_1086; lean_object* x_1087; 
x_1084 = lean_ctor_get(x_1081, 1);
x_1085 = 0;
x_1086 = l_Lake_BuildTrace_nil;
x_1087 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_1087, 0, x_1084);
lean_ctor_set(x_1087, 1, x_1086);
lean_ctor_set_uint8(x_1087, sizeof(void*)*2, x_1085);
lean_ctor_set(x_1081, 1, x_1087);
x_1064 = x_1081;
x_1065 = x_1082;
goto block_1080;
}
else
{
lean_object* x_1088; lean_object* x_1089; uint8_t x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; 
x_1088 = lean_ctor_get(x_1081, 0);
x_1089 = lean_ctor_get(x_1081, 1);
lean_inc(x_1089);
lean_inc(x_1088);
lean_dec(x_1081);
x_1090 = 0;
x_1091 = l_Lake_BuildTrace_nil;
x_1092 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_1092, 0, x_1089);
lean_ctor_set(x_1092, 1, x_1091);
lean_ctor_set_uint8(x_1092, sizeof(void*)*2, x_1090);
x_1093 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1093, 0, x_1088);
lean_ctor_set(x_1093, 1, x_1092);
x_1064 = x_1093;
x_1065 = x_1082;
goto block_1080;
}
}
else
{
uint8_t x_1094; 
x_1094 = !lean_is_exclusive(x_1081);
if (x_1094 == 0)
{
lean_object* x_1095; uint8_t x_1096; lean_object* x_1097; lean_object* x_1098; 
x_1095 = lean_ctor_get(x_1081, 1);
x_1096 = 0;
x_1097 = l_Lake_BuildTrace_nil;
x_1098 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_1098, 0, x_1095);
lean_ctor_set(x_1098, 1, x_1097);
lean_ctor_set_uint8(x_1098, sizeof(void*)*2, x_1096);
lean_ctor_set(x_1081, 1, x_1098);
x_1064 = x_1081;
x_1065 = x_1082;
goto block_1080;
}
else
{
lean_object* x_1099; lean_object* x_1100; uint8_t x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; 
x_1099 = lean_ctor_get(x_1081, 0);
x_1100 = lean_ctor_get(x_1081, 1);
lean_inc(x_1100);
lean_inc(x_1099);
lean_dec(x_1081);
x_1101 = 0;
x_1102 = l_Lake_BuildTrace_nil;
x_1103 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_1103, 0, x_1100);
lean_ctor_set(x_1103, 1, x_1102);
lean_ctor_set_uint8(x_1103, sizeof(void*)*2, x_1101);
x_1104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1104, 0, x_1099);
lean_ctor_set(x_1104, 1, x_1103);
x_1064 = x_1104;
x_1065 = x_1082;
goto block_1080;
}
}
}
}
}
static lean_object* _init_l_Lake_LeanLib_recBuildShared___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":shared", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildShared(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = 1;
x_12 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___spec__2___closed__1;
lean_inc(x_9);
x_13 = l_Lean_Name_toString(x_9, x_11, x_12);
x_14 = l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__1;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = l_Lake_LeanLib_recBuildShared___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
lean_inc(x_9);
lean_inc(x_18);
x_19 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_9);
x_20 = l_Lake_LeanLib_modulesFacetConfig___closed__2;
x_21 = l_Lake_LeanLib_modulesFacet;
lean_inc(x_1);
x_22 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_1);
lean_ctor_set(x_22, 3, x_21);
x_23 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_23, 0, x_22);
lean_closure_set(x_23, 1, lean_box(0));
x_24 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildShared___lambda__1___boxed), 13, 6);
lean_closure_set(x_24, 0, x_10);
lean_closure_set(x_24, 1, x_8);
lean_closure_set(x_24, 2, x_1);
lean_closure_set(x_24, 3, x_18);
lean_closure_set(x_24, 4, x_9);
lean_closure_set(x_24, 5, x_20);
x_25 = lean_alloc_closure((void*)(l_Lake_EquipT_bind___at_Lake_LeanLib_recCollectLocalModules___spec__2___rarg), 8, 2);
lean_closure_set(x_25, 0, x_23);
lean_closure_set(x_25, 1, x_24);
x_26 = 0;
x_27 = l_Lake_withRegisterJob___at_Lake_LeanLib_recBuildShared___spec__16(x_17, x_25, x_26, x_2, x_3, x_4, x_5, x_6, x_7);
return x_27;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__2(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__3(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__4(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__5(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__6(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__7(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__10(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at_Lake_LeanLib_recBuildShared___spec__8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_OrdHashSet_appendArray___at_Lake_LeanLib_recBuildShared___spec__8(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__11(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__13(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLib_recBuildShared___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_mapMUnsafe_map___at_Lake_LeanLib_recBuildShared___spec__14(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildShared___spec__15(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recBuildShared___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recBuildShared___spec__18(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_withRegisterJob___at_Lake_LeanLib_recBuildShared___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lake_withRegisterJob___at_Lake_LeanLib_recBuildShared___spec__16(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildShared___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lake_LeanLib_recBuildShared___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_LeanLib_sharedFacetConfig___spec__1(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l_Lean_Json_compress(x_5);
return x_6;
}
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildShared), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_stdFormat___at_Lake_LeanLib_sharedFacetConfig___spec__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lake_LeanLib_modulesFacetConfig___closed__2;
x_2 = l_Lake_LeanLib_sharedFacetConfig___closed__1;
x_3 = l_Lake_instDataKindDynlib;
x_4 = 1;
x_5 = l_Lake_LeanLib_sharedFacetConfig___closed__2;
x_6 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_4);
return x_6;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_LeanLib_sharedFacetConfig___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at_Lake_LeanLib_sharedFacetConfig___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_stdFormat___at_Lake_LeanLib_sharedFacetConfig___spec__1(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildExtraDepTargets___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_3, x_4);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_array_uget(x_2, x_3);
x_14 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_13);
lean_inc(x_1);
x_15 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(x_1, x_13, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lake_Job_toOpaque___rarg(x_20);
x_22 = l_Lake_Job_mix___rarg(x_5, x_21);
x_23 = 1;
x_24 = lean_usize_add(x_3, x_23);
x_3 = x_24;
x_5 = x_22;
x_10 = x_19;
x_11 = x_17;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_15);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_15, 0);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_16);
if (x_28 == 0)
{
return x_15;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_16);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_15, 0, x_31);
return x_15;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_dec(x_15);
x_33 = lean_ctor_get(x_16, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_16, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_35 = x_16;
} else {
 lean_dec_ref(x_16);
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
else
{
uint8_t x_38; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_15);
if (x_38 == 0)
{
return x_15;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_15, 0);
x_40 = lean_ctor_get(x_15, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_15);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_5);
lean_ctor_set(x_42, 1, x_10);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_11);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildExtraDepTargets___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_3, x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_uget(x_2, x_3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_14 = l_Lake_Package_fetchTargetJob(x_1, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_Lake_Job_mix___rarg(x_5, x_17);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_5 = x_19;
x_10 = x_18;
x_11 = x_16;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_14, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
return x_14;
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
lean_ctor_set(x_14, 0, x_28);
return x_14;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_dec(x_14);
x_30 = lean_ctor_get(x_15, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_32 = x_15;
} else {
 lean_dec_ref(x_15);
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
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_5);
lean_ctor_set(x_39, 1, x_10);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_11);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildExtraDepTargets(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Lake_Package_keyword;
x_12 = l_Lake_Package_extraDepFacet;
lean_inc(x_8);
x_13 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_8);
lean_ctor_set(x_13, 3, x_12);
lean_inc(x_2);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = lean_apply_6(x_2, x_13, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
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
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_107 = lean_ctor_get(x_1, 2);
lean_inc(x_107);
x_108 = lean_ctor_get(x_107, 6);
lean_inc(x_108);
lean_dec(x_107);
x_109 = lean_array_get_size(x_108);
x_110 = lean_unsigned_to_nat(0u);
x_111 = lean_nat_dec_lt(x_110, x_109);
if (x_111 == 0)
{
lean_dec(x_109);
lean_dec(x_108);
x_21 = x_15;
x_22 = x_16;
goto block_106;
}
else
{
uint8_t x_112; 
x_112 = lean_nat_dec_le(x_109, x_109);
if (x_112 == 0)
{
lean_dec(x_109);
lean_dec(x_108);
x_21 = x_15;
x_22 = x_16;
goto block_106;
}
else
{
size_t x_113; size_t x_114; lean_object* x_115; 
lean_free_object(x_15);
x_113 = 0;
x_114 = lean_usize_of_nat(x_109);
lean_dec(x_109);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_8);
x_115 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildExtraDepTargets___spec__2(x_8, x_108, x_113, x_114, x_19, x_2, x_3, x_4, x_5, x_20, x_16);
lean_dec(x_108);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_21 = x_116;
x_22 = x_117;
goto block_106;
}
else
{
uint8_t x_118; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_115);
if (x_118 == 0)
{
return x_115;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_115, 0);
x_120 = lean_ctor_get(x_115, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_115);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
}
block_106:
{
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
x_26 = lean_ctor_get(x_1, 2);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_ctor_get(x_26, 5);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_array_get_size(x_27);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_nat_dec_lt(x_29, x_28);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_17)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_17;
}
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_22);
return x_31;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_28, x_28);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_17)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_17;
}
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_22);
return x_33;
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; 
lean_free_object(x_21);
lean_dec(x_17);
x_34 = 0;
x_35 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_36 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildExtraDepTargets___spec__1(x_8, x_27, x_34, x_35, x_24, x_2, x_3, x_4, x_5, x_25, x_22);
lean_dec(x_27);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_36, 0);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 0);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_37);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_36, 0, x_43);
return x_36;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_36, 1);
lean_inc(x_44);
lean_dec(x_36);
x_45 = lean_ctor_get(x_37, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_47 = x_37;
} else {
 lean_dec_ref(x_37);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
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
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_36);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_36, 0);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_37);
if (x_52 == 0)
{
return x_36;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_37, 0);
x_54 = lean_ctor_get(x_37, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_37);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_36, 0, x_55);
return x_36;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_36, 1);
lean_inc(x_56);
lean_dec(x_36);
x_57 = lean_ctor_get(x_37, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_37, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_59 = x_37;
} else {
 lean_dec_ref(x_37);
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
x_62 = !lean_is_exclusive(x_36);
if (x_62 == 0)
{
return x_36;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_36, 0);
x_64 = lean_ctor_get(x_36, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_36);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_66 = lean_ctor_get(x_21, 0);
x_67 = lean_ctor_get(x_21, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_21);
x_68 = lean_ctor_get(x_1, 2);
lean_inc(x_68);
lean_dec(x_1);
x_69 = lean_ctor_get(x_68, 5);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_array_get_size(x_69);
x_71 = lean_unsigned_to_nat(0u);
x_72 = lean_nat_dec_lt(x_71, x_70);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_66);
lean_ctor_set(x_73, 1, x_67);
if (lean_is_scalar(x_17)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_17;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_22);
return x_74;
}
else
{
uint8_t x_75; 
x_75 = lean_nat_dec_le(x_70, x_70);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_66);
lean_ctor_set(x_76, 1, x_67);
if (lean_is_scalar(x_17)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_17;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_22);
return x_77;
}
else
{
size_t x_78; size_t x_79; lean_object* x_80; 
lean_dec(x_17);
x_78 = 0;
x_79 = lean_usize_of_nat(x_70);
lean_dec(x_70);
x_80 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildExtraDepTargets___spec__1(x_8, x_69, x_78, x_79, x_66, x_2, x_3, x_4, x_5, x_67, x_22);
lean_dec(x_69);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
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
x_84 = lean_ctor_get(x_81, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_86 = x_81;
} else {
 lean_dec_ref(x_81);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
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
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_89 = lean_ctor_get(x_80, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_90 = x_80;
} else {
 lean_dec_ref(x_80);
 x_90 = lean_box(0);
}
x_91 = lean_ctor_get(x_81, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_81, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_93 = x_81;
} else {
 lean_dec_ref(x_81);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
if (lean_is_scalar(x_90)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_90;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_89);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
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
}
}
else
{
uint8_t x_100; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_21);
if (x_100 == 0)
{
lean_object* x_101; 
if (lean_is_scalar(x_17)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_17;
}
lean_ctor_set(x_101, 0, x_21);
lean_ctor_set(x_101, 1, x_22);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_21, 0);
x_103 = lean_ctor_get(x_21, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_21);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
if (lean_is_scalar(x_17)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_17;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_22);
return x_105;
}
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_122 = lean_ctor_get(x_15, 0);
x_123 = lean_ctor_get(x_15, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_15);
x_167 = lean_ctor_get(x_1, 2);
lean_inc(x_167);
x_168 = lean_ctor_get(x_167, 6);
lean_inc(x_168);
lean_dec(x_167);
x_169 = lean_array_get_size(x_168);
x_170 = lean_unsigned_to_nat(0u);
x_171 = lean_nat_dec_lt(x_170, x_169);
if (x_171 == 0)
{
lean_object* x_172; 
lean_dec(x_169);
lean_dec(x_168);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_122);
lean_ctor_set(x_172, 1, x_123);
x_124 = x_172;
x_125 = x_16;
goto block_166;
}
else
{
uint8_t x_173; 
x_173 = lean_nat_dec_le(x_169, x_169);
if (x_173 == 0)
{
lean_object* x_174; 
lean_dec(x_169);
lean_dec(x_168);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_122);
lean_ctor_set(x_174, 1, x_123);
x_124 = x_174;
x_125 = x_16;
goto block_166;
}
else
{
size_t x_175; size_t x_176; lean_object* x_177; 
x_175 = 0;
x_176 = lean_usize_of_nat(x_169);
lean_dec(x_169);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_8);
x_177 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildExtraDepTargets___spec__2(x_8, x_168, x_175, x_176, x_122, x_2, x_3, x_4, x_5, x_123, x_16);
lean_dec(x_168);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_124 = x_178;
x_125 = x_179;
goto block_166;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_180 = lean_ctor_get(x_177, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_177, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_182 = x_177;
} else {
 lean_dec_ref(x_177);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(1, 2, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_181);
return x_183;
}
}
}
block_166:
{
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_128 = x_124;
} else {
 lean_dec_ref(x_124);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_1, 2);
lean_inc(x_129);
lean_dec(x_1);
x_130 = lean_ctor_get(x_129, 5);
lean_inc(x_130);
lean_dec(x_129);
x_131 = lean_array_get_size(x_130);
x_132 = lean_unsigned_to_nat(0u);
x_133 = lean_nat_dec_lt(x_132, x_131);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_128)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_128;
}
lean_ctor_set(x_134, 0, x_126);
lean_ctor_set(x_134, 1, x_127);
if (lean_is_scalar(x_17)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_17;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_125);
return x_135;
}
else
{
uint8_t x_136; 
x_136 = lean_nat_dec_le(x_131, x_131);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_128)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_128;
}
lean_ctor_set(x_137, 0, x_126);
lean_ctor_set(x_137, 1, x_127);
if (lean_is_scalar(x_17)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_17;
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_125);
return x_138;
}
else
{
size_t x_139; size_t x_140; lean_object* x_141; 
lean_dec(x_128);
lean_dec(x_17);
x_139 = 0;
x_140 = lean_usize_of_nat(x_131);
lean_dec(x_131);
x_141 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildExtraDepTargets___spec__1(x_8, x_130, x_139, x_140, x_126, x_2, x_3, x_4, x_5, x_127, x_125);
lean_dec(x_130);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_144 = x_141;
} else {
 lean_dec_ref(x_141);
 x_144 = lean_box(0);
}
x_145 = lean_ctor_get(x_142, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_142, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_147 = x_142;
} else {
 lean_dec_ref(x_142);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_146);
if (lean_is_scalar(x_144)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_144;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_143);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_150 = lean_ctor_get(x_141, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_151 = x_141;
} else {
 lean_dec_ref(x_141);
 x_151 = lean_box(0);
}
x_152 = lean_ctor_get(x_142, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_142, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_154 = x_142;
} else {
 lean_dec_ref(x_142);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_153);
if (lean_is_scalar(x_151)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_151;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_150);
return x_156;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_157 = lean_ctor_get(x_141, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_141, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_159 = x_141;
} else {
 lean_dec_ref(x_141);
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
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_161 = lean_ctor_get(x_124, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_124, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_163 = x_124;
} else {
 lean_dec_ref(x_124);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
if (lean_is_scalar(x_17)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_17;
}
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_125);
return x_165;
}
}
}
}
else
{
uint8_t x_184; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_184 = !lean_is_exclusive(x_14);
if (x_184 == 0)
{
lean_object* x_185; uint8_t x_186; 
x_185 = lean_ctor_get(x_14, 0);
lean_dec(x_185);
x_186 = !lean_is_exclusive(x_15);
if (x_186 == 0)
{
return x_14;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_15, 0);
x_188 = lean_ctor_get(x_15, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_15);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
lean_ctor_set(x_14, 0, x_189);
return x_14;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_190 = lean_ctor_get(x_14, 1);
lean_inc(x_190);
lean_dec(x_14);
x_191 = lean_ctor_get(x_15, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_15, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_193 = x_15;
} else {
 lean_dec_ref(x_15);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_192);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_190);
return x_195;
}
}
}
else
{
uint8_t x_196; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_196 = !lean_is_exclusive(x_14);
if (x_196 == 0)
{
return x_14;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_14, 0);
x_198 = lean_ctor_get(x_14, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_14);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildExtraDepTargets___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildExtraDepTargets___spec__1(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildExtraDepTargets___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_recBuildExtraDepTargets___spec__2(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildExtraDepTargets), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lake_LeanLib_modulesFacetConfig___closed__2;
x_2 = l_Lake_LeanLib_extraDepFacetConfig___closed__1;
x_3 = l_Lake_instDataKindUnit;
x_4 = 1;
x_5 = l_Lake_LeanLib_leanArtsFacetConfig___closed__2;
x_6 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_4);
return x_6;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_LeanLib_extraDepFacetConfig___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLib_recBuildDefaultFacets___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_array_uget(x_4, x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_4, x_3, x_15);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lake_LeanLib_modulesFacetConfig___closed__2;
lean_inc(x_1);
x_22 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_1);
lean_ctor_set(x_22, 3, x_14);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_23 = lean_apply_6(x_5, x_22, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = l_Lake_Job_toOpaque___rarg(x_26);
x_29 = 1;
x_30 = lean_usize_add(x_3, x_29);
x_31 = lean_array_uset(x_16, x_3, x_28);
x_3 = x_30;
x_4 = x_31;
x_9 = x_27;
x_10 = x_25;
goto _start;
}
else
{
uint8_t x_33; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_23);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_23, 0);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_24);
if (x_35 == 0)
{
return x_23;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_24, 0);
x_37 = lean_ctor_get(x_24, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_24);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_23, 0, x_38);
return x_23;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_23, 1);
lean_inc(x_39);
lean_dec(x_23);
x_40 = lean_ctor_get(x_24, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_24, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_42 = x_24;
} else {
 lean_dec_ref(x_24);
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
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_23);
if (x_45 == 0)
{
return x_23;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_23, 0);
x_47 = lean_ctor_get(x_23, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_23);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildDefaultFacets(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 7);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_array_size(x_9);
x_11 = 0;
x_12 = l_Array_mapMUnsafe_map___at_Lake_LeanLib_recBuildDefaultFacets___spec__1(x_1, x_10, x_11, x_9, x_2, x_3, x_4, x_5, x_6, x_7);
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
x_18 = l_Lake_Job_mixArray___rarg(x_17);
lean_dec(x_17);
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
x_21 = l_Lake_Job_mixArray___rarg(x_19);
lean_dec(x_19);
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
x_27 = l_Lake_Job_mixArray___rarg(x_24);
lean_dec(x_24);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLib_recBuildDefaultFacets___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_mapMUnsafe_map___at_Lake_LeanLib_recBuildDefaultFacets___spec__1(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
static lean_object* _init_l_Lake_LeanLib_defaultFacetConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildDefaultFacets), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_defaultFacetConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lake_LeanLib_modulesFacetConfig___closed__2;
x_2 = l_Lake_LeanLib_defaultFacetConfig___closed__1;
x_3 = l_Lake_instDataKindUnit;
x_4 = 1;
x_5 = l_Lake_LeanLib_leanArtsFacetConfig___closed__2;
x_6 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_4);
return x_6;
}
}
static lean_object* _init_l_Lake_LeanLib_defaultFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_LeanLib_defaultFacetConfig___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lake_LeanLib_initFacetConfigs___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = 0;
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = l_Lean_Name_quickCmp(x_2, x_10);
switch (x_13) {
case 0:
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_RBNode_ins___at_Lake_LeanLib_initFacetConfigs___spec__2(x_9, x_2, x_3);
x_15 = 0;
lean_ctor_set(x_1, 0, x_14);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_15);
return x_1;
}
case 1:
{
uint8_t x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = 0;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_16);
return x_1;
}
default: 
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_RBNode_ins___at_Lake_LeanLib_initFacetConfigs___spec__2(x_12, x_2, x_3);
x_18 = 0;
lean_ctor_set(x_1, 3, x_17);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_18);
return x_1;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 2);
x_22 = lean_ctor_get(x_1, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_23 = l_Lean_Name_quickCmp(x_2, x_20);
switch (x_23) {
case 0:
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = l_Lean_RBNode_ins___at_Lake_LeanLib_initFacetConfigs___spec__2(x_19, x_2, x_3);
x_25 = 0;
x_26 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_21);
lean_ctor_set(x_26, 3, x_22);
lean_ctor_set_uint8(x_26, sizeof(void*)*4, x_25);
return x_26;
}
case 1:
{
uint8_t x_27; lean_object* x_28; 
lean_dec(x_21);
lean_dec(x_20);
x_27 = 0;
x_28 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set(x_28, 2, x_3);
lean_ctor_set(x_28, 3, x_22);
lean_ctor_set_uint8(x_28, sizeof(void*)*4, x_27);
return x_28;
}
default: 
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = l_Lean_RBNode_ins___at_Lake_LeanLib_initFacetConfigs___spec__2(x_22, x_2, x_3);
x_30 = 0;
x_31 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_20);
lean_ctor_set(x_31, 2, x_21);
lean_ctor_set(x_31, 3, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_30);
return x_31;
}
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_1, 0);
x_34 = lean_ctor_get(x_1, 1);
x_35 = lean_ctor_get(x_1, 2);
x_36 = lean_ctor_get(x_1, 3);
x_37 = l_Lean_Name_quickCmp(x_2, x_34);
switch (x_37) {
case 0:
{
lean_object* x_38; uint8_t x_39; 
x_38 = l_Lean_RBNode_ins___at_Lake_LeanLib_initFacetConfigs___spec__2(x_33, x_2, x_3);
x_39 = lean_ctor_get_uint8(x_38, sizeof(void*)*4);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_38, 3);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_38, 3);
lean_dec(x_43);
x_44 = lean_ctor_get(x_38, 0);
lean_dec(x_44);
lean_ctor_set(x_38, 0, x_41);
x_45 = 1;
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_45);
return x_1;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_38, 1);
x_47 = lean_ctor_get(x_38, 2);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_38);
x_48 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set(x_48, 2, x_47);
lean_ctor_set(x_48, 3, x_41);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_39);
x_49 = 1;
lean_ctor_set(x_1, 0, x_48);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
uint8_t x_50; 
x_50 = lean_ctor_get_uint8(x_41, sizeof(void*)*4);
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_38);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_38, 1);
x_53 = lean_ctor_get(x_38, 2);
x_54 = lean_ctor_get(x_38, 3);
lean_dec(x_54);
x_55 = lean_ctor_get(x_38, 0);
lean_dec(x_55);
x_56 = !lean_is_exclusive(x_41);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_62; 
x_57 = lean_ctor_get(x_41, 0);
x_58 = lean_ctor_get(x_41, 1);
x_59 = lean_ctor_get(x_41, 2);
x_60 = lean_ctor_get(x_41, 3);
x_61 = 1;
lean_ctor_set(x_41, 3, x_57);
lean_ctor_set(x_41, 2, x_53);
lean_ctor_set(x_41, 1, x_52);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_61);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 0, x_60);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_61);
x_62 = 0;
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_59);
lean_ctor_set(x_1, 1, x_58);
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_62);
return x_1;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; uint8_t x_69; 
x_63 = lean_ctor_get(x_41, 0);
x_64 = lean_ctor_get(x_41, 1);
x_65 = lean_ctor_get(x_41, 2);
x_66 = lean_ctor_get(x_41, 3);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_41);
x_67 = 1;
x_68 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_68, 0, x_40);
lean_ctor_set(x_68, 1, x_52);
lean_ctor_set(x_68, 2, x_53);
lean_ctor_set(x_68, 3, x_63);
lean_ctor_set_uint8(x_68, sizeof(void*)*4, x_67);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 0, x_66);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_67);
x_69 = 0;
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_65);
lean_ctor_set(x_1, 1, x_64);
lean_ctor_set(x_1, 0, x_68);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_69);
return x_1;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_70 = lean_ctor_get(x_38, 1);
x_71 = lean_ctor_get(x_38, 2);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_38);
x_72 = lean_ctor_get(x_41, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_41, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_41, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_41, 3);
lean_inc(x_75);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 x_76 = x_41;
} else {
 lean_dec_ref(x_41);
 x_76 = lean_box(0);
}
x_77 = 1;
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(1, 4, 1);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_40);
lean_ctor_set(x_78, 1, x_70);
lean_ctor_set(x_78, 2, x_71);
lean_ctor_set(x_78, 3, x_72);
lean_ctor_set_uint8(x_78, sizeof(void*)*4, x_77);
x_79 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_34);
lean_ctor_set(x_79, 2, x_35);
lean_ctor_set(x_79, 3, x_36);
lean_ctor_set_uint8(x_79, sizeof(void*)*4, x_77);
x_80 = 0;
lean_ctor_set(x_1, 3, x_79);
lean_ctor_set(x_1, 2, x_74);
lean_ctor_set(x_1, 1, x_73);
lean_ctor_set(x_1, 0, x_78);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_80);
return x_1;
}
}
else
{
uint8_t x_81; 
lean_free_object(x_1);
x_81 = !lean_is_exclusive(x_41);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_82 = lean_ctor_get(x_41, 3);
lean_dec(x_82);
x_83 = lean_ctor_get(x_41, 2);
lean_dec(x_83);
x_84 = lean_ctor_get(x_41, 1);
lean_dec(x_84);
x_85 = lean_ctor_get(x_41, 0);
lean_dec(x_85);
x_86 = 1;
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_86);
return x_41;
}
else
{
uint8_t x_87; lean_object* x_88; 
lean_dec(x_41);
x_87 = 1;
x_88 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_88, 0, x_38);
lean_ctor_set(x_88, 1, x_34);
lean_ctor_set(x_88, 2, x_35);
lean_ctor_set(x_88, 3, x_36);
lean_ctor_set_uint8(x_88, sizeof(void*)*4, x_87);
return x_88;
}
}
}
}
else
{
uint8_t x_89; 
x_89 = lean_ctor_get_uint8(x_40, sizeof(void*)*4);
if (x_89 == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_38);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_91 = lean_ctor_get(x_38, 1);
x_92 = lean_ctor_get(x_38, 2);
x_93 = lean_ctor_get(x_38, 3);
x_94 = lean_ctor_get(x_38, 0);
lean_dec(x_94);
x_95 = !lean_is_exclusive(x_40);
if (x_95 == 0)
{
uint8_t x_96; uint8_t x_97; 
x_96 = 1;
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_96);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 0, x_93);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_96);
x_97 = 0;
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_92);
lean_ctor_set(x_1, 1, x_91);
lean_ctor_set(x_1, 0, x_40);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_97);
return x_1;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; uint8_t x_104; 
x_98 = lean_ctor_get(x_40, 0);
x_99 = lean_ctor_get(x_40, 1);
x_100 = lean_ctor_get(x_40, 2);
x_101 = lean_ctor_get(x_40, 3);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_40);
x_102 = 1;
x_103 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set(x_103, 1, x_99);
lean_ctor_set(x_103, 2, x_100);
lean_ctor_set(x_103, 3, x_101);
lean_ctor_set_uint8(x_103, sizeof(void*)*4, x_102);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 0, x_93);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_102);
x_104 = 0;
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_92);
lean_ctor_set(x_1, 1, x_91);
lean_ctor_set(x_1, 0, x_103);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_104);
return x_1;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_105 = lean_ctor_get(x_38, 1);
x_106 = lean_ctor_get(x_38, 2);
x_107 = lean_ctor_get(x_38, 3);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_38);
x_108 = lean_ctor_get(x_40, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_40, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_40, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_40, 3);
lean_inc(x_111);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_112 = x_40;
} else {
 lean_dec_ref(x_40);
 x_112 = lean_box(0);
}
x_113 = 1;
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(1, 4, 1);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_108);
lean_ctor_set(x_114, 1, x_109);
lean_ctor_set(x_114, 2, x_110);
lean_ctor_set(x_114, 3, x_111);
lean_ctor_set_uint8(x_114, sizeof(void*)*4, x_113);
x_115 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_115, 0, x_107);
lean_ctor_set(x_115, 1, x_34);
lean_ctor_set(x_115, 2, x_35);
lean_ctor_set(x_115, 3, x_36);
lean_ctor_set_uint8(x_115, sizeof(void*)*4, x_113);
x_116 = 0;
lean_ctor_set(x_1, 3, x_115);
lean_ctor_set(x_1, 2, x_106);
lean_ctor_set(x_1, 1, x_105);
lean_ctor_set(x_1, 0, x_114);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_116);
return x_1;
}
}
else
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_38, 3);
lean_inc(x_117);
if (lean_obj_tag(x_117) == 0)
{
uint8_t x_118; 
lean_free_object(x_1);
x_118 = !lean_is_exclusive(x_40);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_119 = lean_ctor_get(x_40, 3);
lean_dec(x_119);
x_120 = lean_ctor_get(x_40, 2);
lean_dec(x_120);
x_121 = lean_ctor_get(x_40, 1);
lean_dec(x_121);
x_122 = lean_ctor_get(x_40, 0);
lean_dec(x_122);
x_123 = 1;
lean_ctor_set(x_40, 3, x_36);
lean_ctor_set(x_40, 2, x_35);
lean_ctor_set(x_40, 1, x_34);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_123);
return x_40;
}
else
{
uint8_t x_124; lean_object* x_125; 
lean_dec(x_40);
x_124 = 1;
x_125 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_125, 0, x_38);
lean_ctor_set(x_125, 1, x_34);
lean_ctor_set(x_125, 2, x_35);
lean_ctor_set(x_125, 3, x_36);
lean_ctor_set_uint8(x_125, sizeof(void*)*4, x_124);
return x_125;
}
}
else
{
uint8_t x_126; 
x_126 = lean_ctor_get_uint8(x_117, sizeof(void*)*4);
if (x_126 == 0)
{
uint8_t x_127; 
lean_free_object(x_1);
x_127 = !lean_is_exclusive(x_38);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_128 = lean_ctor_get(x_38, 1);
x_129 = lean_ctor_get(x_38, 2);
x_130 = lean_ctor_get(x_38, 3);
lean_dec(x_130);
x_131 = lean_ctor_get(x_38, 0);
lean_dec(x_131);
x_132 = !lean_is_exclusive(x_117);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; uint8_t x_138; 
x_133 = lean_ctor_get(x_117, 0);
x_134 = lean_ctor_get(x_117, 1);
x_135 = lean_ctor_get(x_117, 2);
x_136 = lean_ctor_get(x_117, 3);
x_137 = 1;
lean_inc(x_40);
lean_ctor_set(x_117, 3, x_133);
lean_ctor_set(x_117, 2, x_129);
lean_ctor_set(x_117, 1, x_128);
lean_ctor_set(x_117, 0, x_40);
x_138 = !lean_is_exclusive(x_40);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_139 = lean_ctor_get(x_40, 3);
lean_dec(x_139);
x_140 = lean_ctor_get(x_40, 2);
lean_dec(x_140);
x_141 = lean_ctor_get(x_40, 1);
lean_dec(x_141);
x_142 = lean_ctor_get(x_40, 0);
lean_dec(x_142);
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_137);
lean_ctor_set(x_40, 3, x_36);
lean_ctor_set(x_40, 2, x_35);
lean_ctor_set(x_40, 1, x_34);
lean_ctor_set(x_40, 0, x_136);
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_137);
x_143 = 0;
lean_ctor_set(x_38, 3, x_40);
lean_ctor_set(x_38, 2, x_135);
lean_ctor_set(x_38, 1, x_134);
lean_ctor_set(x_38, 0, x_117);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_143);
return x_38;
}
else
{
lean_object* x_144; uint8_t x_145; 
lean_dec(x_40);
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_137);
x_144 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_144, 0, x_136);
lean_ctor_set(x_144, 1, x_34);
lean_ctor_set(x_144, 2, x_35);
lean_ctor_set(x_144, 3, x_36);
lean_ctor_set_uint8(x_144, sizeof(void*)*4, x_137);
x_145 = 0;
lean_ctor_set(x_38, 3, x_144);
lean_ctor_set(x_38, 2, x_135);
lean_ctor_set(x_38, 1, x_134);
lean_ctor_set(x_38, 0, x_117);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_145);
return x_38;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_146 = lean_ctor_get(x_117, 0);
x_147 = lean_ctor_get(x_117, 1);
x_148 = lean_ctor_get(x_117, 2);
x_149 = lean_ctor_get(x_117, 3);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_117);
x_150 = 1;
lean_inc(x_40);
x_151 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_151, 0, x_40);
lean_ctor_set(x_151, 1, x_128);
lean_ctor_set(x_151, 2, x_129);
lean_ctor_set(x_151, 3, x_146);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_152 = x_40;
} else {
 lean_dec_ref(x_40);
 x_152 = lean_box(0);
}
lean_ctor_set_uint8(x_151, sizeof(void*)*4, x_150);
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 4, 1);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_149);
lean_ctor_set(x_153, 1, x_34);
lean_ctor_set(x_153, 2, x_35);
lean_ctor_set(x_153, 3, x_36);
lean_ctor_set_uint8(x_153, sizeof(void*)*4, x_150);
x_154 = 0;
lean_ctor_set(x_38, 3, x_153);
lean_ctor_set(x_38, 2, x_148);
lean_ctor_set(x_38, 1, x_147);
lean_ctor_set(x_38, 0, x_151);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_154);
return x_38;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; 
x_155 = lean_ctor_get(x_38, 1);
x_156 = lean_ctor_get(x_38, 2);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_38);
x_157 = lean_ctor_get(x_117, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_117, 1);
lean_inc(x_158);
x_159 = lean_ctor_get(x_117, 2);
lean_inc(x_159);
x_160 = lean_ctor_get(x_117, 3);
lean_inc(x_160);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 lean_ctor_release(x_117, 2);
 lean_ctor_release(x_117, 3);
 x_161 = x_117;
} else {
 lean_dec_ref(x_117);
 x_161 = lean_box(0);
}
x_162 = 1;
lean_inc(x_40);
if (lean_is_scalar(x_161)) {
 x_163 = lean_alloc_ctor(1, 4, 1);
} else {
 x_163 = x_161;
}
lean_ctor_set(x_163, 0, x_40);
lean_ctor_set(x_163, 1, x_155);
lean_ctor_set(x_163, 2, x_156);
lean_ctor_set(x_163, 3, x_157);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_164 = x_40;
} else {
 lean_dec_ref(x_40);
 x_164 = lean_box(0);
}
lean_ctor_set_uint8(x_163, sizeof(void*)*4, x_162);
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 4, 1);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_160);
lean_ctor_set(x_165, 1, x_34);
lean_ctor_set(x_165, 2, x_35);
lean_ctor_set(x_165, 3, x_36);
lean_ctor_set_uint8(x_165, sizeof(void*)*4, x_162);
x_166 = 0;
x_167 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_167, 0, x_163);
lean_ctor_set(x_167, 1, x_158);
lean_ctor_set(x_167, 2, x_159);
lean_ctor_set(x_167, 3, x_165);
lean_ctor_set_uint8(x_167, sizeof(void*)*4, x_166);
return x_167;
}
}
else
{
uint8_t x_168; 
x_168 = !lean_is_exclusive(x_38);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_169 = lean_ctor_get(x_38, 3);
lean_dec(x_169);
x_170 = lean_ctor_get(x_38, 0);
lean_dec(x_170);
x_171 = !lean_is_exclusive(x_40);
if (x_171 == 0)
{
uint8_t x_172; 
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_126);
x_172 = 1;
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_172);
return x_1;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_173 = lean_ctor_get(x_40, 0);
x_174 = lean_ctor_get(x_40, 1);
x_175 = lean_ctor_get(x_40, 2);
x_176 = lean_ctor_get(x_40, 3);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_40);
x_177 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_177, 0, x_173);
lean_ctor_set(x_177, 1, x_174);
lean_ctor_set(x_177, 2, x_175);
lean_ctor_set(x_177, 3, x_176);
lean_ctor_set_uint8(x_177, sizeof(void*)*4, x_126);
lean_ctor_set(x_38, 0, x_177);
x_178 = 1;
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_178);
return x_1;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_179 = lean_ctor_get(x_38, 1);
x_180 = lean_ctor_get(x_38, 2);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_38);
x_181 = lean_ctor_get(x_40, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_40, 1);
lean_inc(x_182);
x_183 = lean_ctor_get(x_40, 2);
lean_inc(x_183);
x_184 = lean_ctor_get(x_40, 3);
lean_inc(x_184);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_185 = x_40;
} else {
 lean_dec_ref(x_40);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 4, 1);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_181);
lean_ctor_set(x_186, 1, x_182);
lean_ctor_set(x_186, 2, x_183);
lean_ctor_set(x_186, 3, x_184);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_126);
x_187 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_179);
lean_ctor_set(x_187, 2, x_180);
lean_ctor_set(x_187, 3, x_117);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_39);
x_188 = 1;
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_188);
return x_1;
}
}
}
}
}
}
else
{
uint8_t x_189; 
x_189 = 1;
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
case 1:
{
uint8_t x_190; 
lean_dec(x_35);
lean_dec(x_34);
x_190 = 1;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_190);
return x_1;
}
default: 
{
lean_object* x_191; uint8_t x_192; 
x_191 = l_Lean_RBNode_ins___at_Lake_LeanLib_initFacetConfigs___spec__2(x_36, x_2, x_3);
x_192 = lean_ctor_get_uint8(x_191, sizeof(void*)*4);
if (x_192 == 0)
{
lean_object* x_193; 
x_193 = lean_ctor_get(x_191, 0);
lean_inc(x_193);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_191, 3);
lean_inc(x_194);
if (lean_obj_tag(x_194) == 0)
{
uint8_t x_195; 
x_195 = !lean_is_exclusive(x_191);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_196 = lean_ctor_get(x_191, 3);
lean_dec(x_196);
x_197 = lean_ctor_get(x_191, 0);
lean_dec(x_197);
lean_ctor_set(x_191, 0, x_194);
x_198 = 1;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_198);
return x_1;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_199 = lean_ctor_get(x_191, 1);
x_200 = lean_ctor_get(x_191, 2);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_191);
x_201 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_201, 0, x_194);
lean_ctor_set(x_201, 1, x_199);
lean_ctor_set(x_201, 2, x_200);
lean_ctor_set(x_201, 3, x_194);
lean_ctor_set_uint8(x_201, sizeof(void*)*4, x_192);
x_202 = 1;
lean_ctor_set(x_1, 3, x_201);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_202);
return x_1;
}
}
else
{
uint8_t x_203; 
x_203 = lean_ctor_get_uint8(x_194, sizeof(void*)*4);
if (x_203 == 0)
{
uint8_t x_204; 
x_204 = !lean_is_exclusive(x_191);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_205 = lean_ctor_get(x_191, 1);
x_206 = lean_ctor_get(x_191, 2);
x_207 = lean_ctor_get(x_191, 3);
lean_dec(x_207);
x_208 = lean_ctor_get(x_191, 0);
lean_dec(x_208);
x_209 = !lean_is_exclusive(x_194);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; uint8_t x_215; 
x_210 = lean_ctor_get(x_194, 0);
x_211 = lean_ctor_get(x_194, 1);
x_212 = lean_ctor_get(x_194, 2);
x_213 = lean_ctor_get(x_194, 3);
x_214 = 1;
lean_ctor_set(x_194, 3, x_193);
lean_ctor_set(x_194, 2, x_35);
lean_ctor_set(x_194, 1, x_34);
lean_ctor_set(x_194, 0, x_33);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_214);
lean_ctor_set(x_191, 3, x_213);
lean_ctor_set(x_191, 2, x_212);
lean_ctor_set(x_191, 1, x_211);
lean_ctor_set(x_191, 0, x_210);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_214);
x_215 = 0;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set(x_1, 2, x_206);
lean_ctor_set(x_1, 1, x_205);
lean_ctor_set(x_1, 0, x_194);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_215);
return x_1;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; lean_object* x_221; uint8_t x_222; 
x_216 = lean_ctor_get(x_194, 0);
x_217 = lean_ctor_get(x_194, 1);
x_218 = lean_ctor_get(x_194, 2);
x_219 = lean_ctor_get(x_194, 3);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_194);
x_220 = 1;
x_221 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_221, 0, x_33);
lean_ctor_set(x_221, 1, x_34);
lean_ctor_set(x_221, 2, x_35);
lean_ctor_set(x_221, 3, x_193);
lean_ctor_set_uint8(x_221, sizeof(void*)*4, x_220);
lean_ctor_set(x_191, 3, x_219);
lean_ctor_set(x_191, 2, x_218);
lean_ctor_set(x_191, 1, x_217);
lean_ctor_set(x_191, 0, x_216);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_220);
x_222 = 0;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set(x_1, 2, x_206);
lean_ctor_set(x_1, 1, x_205);
lean_ctor_set(x_1, 0, x_221);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_222);
return x_1;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_223 = lean_ctor_get(x_191, 1);
x_224 = lean_ctor_get(x_191, 2);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_191);
x_225 = lean_ctor_get(x_194, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_194, 1);
lean_inc(x_226);
x_227 = lean_ctor_get(x_194, 2);
lean_inc(x_227);
x_228 = lean_ctor_get(x_194, 3);
lean_inc(x_228);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 lean_ctor_release(x_194, 3);
 x_229 = x_194;
} else {
 lean_dec_ref(x_194);
 x_229 = lean_box(0);
}
x_230 = 1;
if (lean_is_scalar(x_229)) {
 x_231 = lean_alloc_ctor(1, 4, 1);
} else {
 x_231 = x_229;
}
lean_ctor_set(x_231, 0, x_33);
lean_ctor_set(x_231, 1, x_34);
lean_ctor_set(x_231, 2, x_35);
lean_ctor_set(x_231, 3, x_193);
lean_ctor_set_uint8(x_231, sizeof(void*)*4, x_230);
x_232 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_232, 0, x_225);
lean_ctor_set(x_232, 1, x_226);
lean_ctor_set(x_232, 2, x_227);
lean_ctor_set(x_232, 3, x_228);
lean_ctor_set_uint8(x_232, sizeof(void*)*4, x_230);
x_233 = 0;
lean_ctor_set(x_1, 3, x_232);
lean_ctor_set(x_1, 2, x_224);
lean_ctor_set(x_1, 1, x_223);
lean_ctor_set(x_1, 0, x_231);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_233);
return x_1;
}
}
else
{
uint8_t x_234; 
lean_free_object(x_1);
x_234 = !lean_is_exclusive(x_194);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
x_235 = lean_ctor_get(x_194, 3);
lean_dec(x_235);
x_236 = lean_ctor_get(x_194, 2);
lean_dec(x_236);
x_237 = lean_ctor_get(x_194, 1);
lean_dec(x_237);
x_238 = lean_ctor_get(x_194, 0);
lean_dec(x_238);
x_239 = 1;
lean_ctor_set(x_194, 3, x_191);
lean_ctor_set(x_194, 2, x_35);
lean_ctor_set(x_194, 1, x_34);
lean_ctor_set(x_194, 0, x_33);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_239);
return x_194;
}
else
{
uint8_t x_240; lean_object* x_241; 
lean_dec(x_194);
x_240 = 1;
x_241 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_241, 0, x_33);
lean_ctor_set(x_241, 1, x_34);
lean_ctor_set(x_241, 2, x_35);
lean_ctor_set(x_241, 3, x_191);
lean_ctor_set_uint8(x_241, sizeof(void*)*4, x_240);
return x_241;
}
}
}
}
else
{
uint8_t x_242; 
x_242 = lean_ctor_get_uint8(x_193, sizeof(void*)*4);
if (x_242 == 0)
{
uint8_t x_243; 
x_243 = !lean_is_exclusive(x_191);
if (x_243 == 0)
{
lean_object* x_244; uint8_t x_245; 
x_244 = lean_ctor_get(x_191, 0);
lean_dec(x_244);
x_245 = !lean_is_exclusive(x_193);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; uint8_t x_251; 
x_246 = lean_ctor_get(x_193, 0);
x_247 = lean_ctor_get(x_193, 1);
x_248 = lean_ctor_get(x_193, 2);
x_249 = lean_ctor_get(x_193, 3);
x_250 = 1;
lean_ctor_set(x_193, 3, x_246);
lean_ctor_set(x_193, 2, x_35);
lean_ctor_set(x_193, 1, x_34);
lean_ctor_set(x_193, 0, x_33);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_250);
lean_ctor_set(x_191, 0, x_249);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_250);
x_251 = 0;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set(x_1, 2, x_248);
lean_ctor_set(x_1, 1, x_247);
lean_ctor_set(x_1, 0, x_193);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_251);
return x_1;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; lean_object* x_257; uint8_t x_258; 
x_252 = lean_ctor_get(x_193, 0);
x_253 = lean_ctor_get(x_193, 1);
x_254 = lean_ctor_get(x_193, 2);
x_255 = lean_ctor_get(x_193, 3);
lean_inc(x_255);
lean_inc(x_254);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_193);
x_256 = 1;
x_257 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_257, 0, x_33);
lean_ctor_set(x_257, 1, x_34);
lean_ctor_set(x_257, 2, x_35);
lean_ctor_set(x_257, 3, x_252);
lean_ctor_set_uint8(x_257, sizeof(void*)*4, x_256);
lean_ctor_set(x_191, 0, x_255);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_256);
x_258 = 0;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set(x_1, 2, x_254);
lean_ctor_set(x_1, 1, x_253);
lean_ctor_set(x_1, 0, x_257);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_258);
return x_1;
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_259 = lean_ctor_get(x_191, 1);
x_260 = lean_ctor_get(x_191, 2);
x_261 = lean_ctor_get(x_191, 3);
lean_inc(x_261);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_191);
x_262 = lean_ctor_get(x_193, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_193, 1);
lean_inc(x_263);
x_264 = lean_ctor_get(x_193, 2);
lean_inc(x_264);
x_265 = lean_ctor_get(x_193, 3);
lean_inc(x_265);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_266 = x_193;
} else {
 lean_dec_ref(x_193);
 x_266 = lean_box(0);
}
x_267 = 1;
if (lean_is_scalar(x_266)) {
 x_268 = lean_alloc_ctor(1, 4, 1);
} else {
 x_268 = x_266;
}
lean_ctor_set(x_268, 0, x_33);
lean_ctor_set(x_268, 1, x_34);
lean_ctor_set(x_268, 2, x_35);
lean_ctor_set(x_268, 3, x_262);
lean_ctor_set_uint8(x_268, sizeof(void*)*4, x_267);
x_269 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_269, 0, x_265);
lean_ctor_set(x_269, 1, x_259);
lean_ctor_set(x_269, 2, x_260);
lean_ctor_set(x_269, 3, x_261);
lean_ctor_set_uint8(x_269, sizeof(void*)*4, x_267);
x_270 = 0;
lean_ctor_set(x_1, 3, x_269);
lean_ctor_set(x_1, 2, x_264);
lean_ctor_set(x_1, 1, x_263);
lean_ctor_set(x_1, 0, x_268);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_270);
return x_1;
}
}
else
{
lean_object* x_271; 
x_271 = lean_ctor_get(x_191, 3);
lean_inc(x_271);
if (lean_obj_tag(x_271) == 0)
{
uint8_t x_272; 
lean_free_object(x_1);
x_272 = !lean_is_exclusive(x_193);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; 
x_273 = lean_ctor_get(x_193, 3);
lean_dec(x_273);
x_274 = lean_ctor_get(x_193, 2);
lean_dec(x_274);
x_275 = lean_ctor_get(x_193, 1);
lean_dec(x_275);
x_276 = lean_ctor_get(x_193, 0);
lean_dec(x_276);
x_277 = 1;
lean_ctor_set(x_193, 3, x_191);
lean_ctor_set(x_193, 2, x_35);
lean_ctor_set(x_193, 1, x_34);
lean_ctor_set(x_193, 0, x_33);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_277);
return x_193;
}
else
{
uint8_t x_278; lean_object* x_279; 
lean_dec(x_193);
x_278 = 1;
x_279 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_279, 0, x_33);
lean_ctor_set(x_279, 1, x_34);
lean_ctor_set(x_279, 2, x_35);
lean_ctor_set(x_279, 3, x_191);
lean_ctor_set_uint8(x_279, sizeof(void*)*4, x_278);
return x_279;
}
}
else
{
uint8_t x_280; 
x_280 = lean_ctor_get_uint8(x_271, sizeof(void*)*4);
if (x_280 == 0)
{
uint8_t x_281; 
lean_free_object(x_1);
x_281 = !lean_is_exclusive(x_191);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; uint8_t x_284; 
x_282 = lean_ctor_get(x_191, 3);
lean_dec(x_282);
x_283 = lean_ctor_get(x_191, 0);
lean_dec(x_283);
x_284 = !lean_is_exclusive(x_271);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; uint8_t x_290; 
x_285 = lean_ctor_get(x_271, 0);
x_286 = lean_ctor_get(x_271, 1);
x_287 = lean_ctor_get(x_271, 2);
x_288 = lean_ctor_get(x_271, 3);
x_289 = 1;
lean_inc(x_193);
lean_ctor_set(x_271, 3, x_193);
lean_ctor_set(x_271, 2, x_35);
lean_ctor_set(x_271, 1, x_34);
lean_ctor_set(x_271, 0, x_33);
x_290 = !lean_is_exclusive(x_193);
if (x_290 == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; 
x_291 = lean_ctor_get(x_193, 3);
lean_dec(x_291);
x_292 = lean_ctor_get(x_193, 2);
lean_dec(x_292);
x_293 = lean_ctor_get(x_193, 1);
lean_dec(x_293);
x_294 = lean_ctor_get(x_193, 0);
lean_dec(x_294);
lean_ctor_set_uint8(x_271, sizeof(void*)*4, x_289);
lean_ctor_set(x_193, 3, x_288);
lean_ctor_set(x_193, 2, x_287);
lean_ctor_set(x_193, 1, x_286);
lean_ctor_set(x_193, 0, x_285);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_289);
x_295 = 0;
lean_ctor_set(x_191, 3, x_193);
lean_ctor_set(x_191, 0, x_271);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_295);
return x_191;
}
else
{
lean_object* x_296; uint8_t x_297; 
lean_dec(x_193);
lean_ctor_set_uint8(x_271, sizeof(void*)*4, x_289);
x_296 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_296, 0, x_285);
lean_ctor_set(x_296, 1, x_286);
lean_ctor_set(x_296, 2, x_287);
lean_ctor_set(x_296, 3, x_288);
lean_ctor_set_uint8(x_296, sizeof(void*)*4, x_289);
x_297 = 0;
lean_ctor_set(x_191, 3, x_296);
lean_ctor_set(x_191, 0, x_271);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_297);
return x_191;
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_298 = lean_ctor_get(x_271, 0);
x_299 = lean_ctor_get(x_271, 1);
x_300 = lean_ctor_get(x_271, 2);
x_301 = lean_ctor_get(x_271, 3);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_inc(x_298);
lean_dec(x_271);
x_302 = 1;
lean_inc(x_193);
x_303 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_303, 0, x_33);
lean_ctor_set(x_303, 1, x_34);
lean_ctor_set(x_303, 2, x_35);
lean_ctor_set(x_303, 3, x_193);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_304 = x_193;
} else {
 lean_dec_ref(x_193);
 x_304 = lean_box(0);
}
lean_ctor_set_uint8(x_303, sizeof(void*)*4, x_302);
if (lean_is_scalar(x_304)) {
 x_305 = lean_alloc_ctor(1, 4, 1);
} else {
 x_305 = x_304;
}
lean_ctor_set(x_305, 0, x_298);
lean_ctor_set(x_305, 1, x_299);
lean_ctor_set(x_305, 2, x_300);
lean_ctor_set(x_305, 3, x_301);
lean_ctor_set_uint8(x_305, sizeof(void*)*4, x_302);
x_306 = 0;
lean_ctor_set(x_191, 3, x_305);
lean_ctor_set(x_191, 0, x_303);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_306);
return x_191;
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; lean_object* x_319; 
x_307 = lean_ctor_get(x_191, 1);
x_308 = lean_ctor_get(x_191, 2);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_191);
x_309 = lean_ctor_get(x_271, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_271, 1);
lean_inc(x_310);
x_311 = lean_ctor_get(x_271, 2);
lean_inc(x_311);
x_312 = lean_ctor_get(x_271, 3);
lean_inc(x_312);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 lean_ctor_release(x_271, 2);
 lean_ctor_release(x_271, 3);
 x_313 = x_271;
} else {
 lean_dec_ref(x_271);
 x_313 = lean_box(0);
}
x_314 = 1;
lean_inc(x_193);
if (lean_is_scalar(x_313)) {
 x_315 = lean_alloc_ctor(1, 4, 1);
} else {
 x_315 = x_313;
}
lean_ctor_set(x_315, 0, x_33);
lean_ctor_set(x_315, 1, x_34);
lean_ctor_set(x_315, 2, x_35);
lean_ctor_set(x_315, 3, x_193);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_316 = x_193;
} else {
 lean_dec_ref(x_193);
 x_316 = lean_box(0);
}
lean_ctor_set_uint8(x_315, sizeof(void*)*4, x_314);
if (lean_is_scalar(x_316)) {
 x_317 = lean_alloc_ctor(1, 4, 1);
} else {
 x_317 = x_316;
}
lean_ctor_set(x_317, 0, x_309);
lean_ctor_set(x_317, 1, x_310);
lean_ctor_set(x_317, 2, x_311);
lean_ctor_set(x_317, 3, x_312);
lean_ctor_set_uint8(x_317, sizeof(void*)*4, x_314);
x_318 = 0;
x_319 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_319, 0, x_315);
lean_ctor_set(x_319, 1, x_307);
lean_ctor_set(x_319, 2, x_308);
lean_ctor_set(x_319, 3, x_317);
lean_ctor_set_uint8(x_319, sizeof(void*)*4, x_318);
return x_319;
}
}
else
{
uint8_t x_320; 
x_320 = !lean_is_exclusive(x_191);
if (x_320 == 0)
{
lean_object* x_321; lean_object* x_322; uint8_t x_323; 
x_321 = lean_ctor_get(x_191, 3);
lean_dec(x_321);
x_322 = lean_ctor_get(x_191, 0);
lean_dec(x_322);
x_323 = !lean_is_exclusive(x_193);
if (x_323 == 0)
{
uint8_t x_324; 
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_280);
x_324 = 1;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_324);
return x_1;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; 
x_325 = lean_ctor_get(x_193, 0);
x_326 = lean_ctor_get(x_193, 1);
x_327 = lean_ctor_get(x_193, 2);
x_328 = lean_ctor_get(x_193, 3);
lean_inc(x_328);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_193);
x_329 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_329, 0, x_325);
lean_ctor_set(x_329, 1, x_326);
lean_ctor_set(x_329, 2, x_327);
lean_ctor_set(x_329, 3, x_328);
lean_ctor_set_uint8(x_329, sizeof(void*)*4, x_280);
lean_ctor_set(x_191, 0, x_329);
x_330 = 1;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_330);
return x_1;
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; uint8_t x_340; 
x_331 = lean_ctor_get(x_191, 1);
x_332 = lean_ctor_get(x_191, 2);
lean_inc(x_332);
lean_inc(x_331);
lean_dec(x_191);
x_333 = lean_ctor_get(x_193, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_193, 1);
lean_inc(x_334);
x_335 = lean_ctor_get(x_193, 2);
lean_inc(x_335);
x_336 = lean_ctor_get(x_193, 3);
lean_inc(x_336);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_337 = x_193;
} else {
 lean_dec_ref(x_193);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 4, 1);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_333);
lean_ctor_set(x_338, 1, x_334);
lean_ctor_set(x_338, 2, x_335);
lean_ctor_set(x_338, 3, x_336);
lean_ctor_set_uint8(x_338, sizeof(void*)*4, x_280);
x_339 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_331);
lean_ctor_set(x_339, 2, x_332);
lean_ctor_set(x_339, 3, x_271);
lean_ctor_set_uint8(x_339, sizeof(void*)*4, x_192);
x_340 = 1;
lean_ctor_set(x_1, 3, x_339);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_340);
return x_1;
}
}
}
}
}
}
else
{
uint8_t x_341; 
x_341 = 1;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_341);
return x_1;
}
}
}
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; 
x_342 = lean_ctor_get(x_1, 0);
x_343 = lean_ctor_get(x_1, 1);
x_344 = lean_ctor_get(x_1, 2);
x_345 = lean_ctor_get(x_1, 3);
lean_inc(x_345);
lean_inc(x_344);
lean_inc(x_343);
lean_inc(x_342);
lean_dec(x_1);
x_346 = l_Lean_Name_quickCmp(x_2, x_343);
switch (x_346) {
case 0:
{
lean_object* x_347; uint8_t x_348; 
x_347 = l_Lean_RBNode_ins___at_Lake_LeanLib_initFacetConfigs___spec__2(x_342, x_2, x_3);
x_348 = lean_ctor_get_uint8(x_347, sizeof(void*)*4);
if (x_348 == 0)
{
lean_object* x_349; 
x_349 = lean_ctor_get(x_347, 0);
lean_inc(x_349);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; 
x_350 = lean_ctor_get(x_347, 3);
lean_inc(x_350);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; lean_object* x_356; 
x_351 = lean_ctor_get(x_347, 1);
lean_inc(x_351);
x_352 = lean_ctor_get(x_347, 2);
lean_inc(x_352);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_353 = x_347;
} else {
 lean_dec_ref(x_347);
 x_353 = lean_box(0);
}
if (lean_is_scalar(x_353)) {
 x_354 = lean_alloc_ctor(1, 4, 1);
} else {
 x_354 = x_353;
}
lean_ctor_set(x_354, 0, x_350);
lean_ctor_set(x_354, 1, x_351);
lean_ctor_set(x_354, 2, x_352);
lean_ctor_set(x_354, 3, x_350);
lean_ctor_set_uint8(x_354, sizeof(void*)*4, x_348);
x_355 = 1;
x_356 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_356, 0, x_354);
lean_ctor_set(x_356, 1, x_343);
lean_ctor_set(x_356, 2, x_344);
lean_ctor_set(x_356, 3, x_345);
lean_ctor_set_uint8(x_356, sizeof(void*)*4, x_355);
return x_356;
}
else
{
uint8_t x_357; 
x_357 = lean_ctor_get_uint8(x_350, sizeof(void*)*4);
if (x_357 == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; lean_object* x_370; 
x_358 = lean_ctor_get(x_347, 1);
lean_inc(x_358);
x_359 = lean_ctor_get(x_347, 2);
lean_inc(x_359);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_360 = x_347;
} else {
 lean_dec_ref(x_347);
 x_360 = lean_box(0);
}
x_361 = lean_ctor_get(x_350, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_350, 1);
lean_inc(x_362);
x_363 = lean_ctor_get(x_350, 2);
lean_inc(x_363);
x_364 = lean_ctor_get(x_350, 3);
lean_inc(x_364);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_365 = x_350;
} else {
 lean_dec_ref(x_350);
 x_365 = lean_box(0);
}
x_366 = 1;
if (lean_is_scalar(x_365)) {
 x_367 = lean_alloc_ctor(1, 4, 1);
} else {
 x_367 = x_365;
}
lean_ctor_set(x_367, 0, x_349);
lean_ctor_set(x_367, 1, x_358);
lean_ctor_set(x_367, 2, x_359);
lean_ctor_set(x_367, 3, x_361);
lean_ctor_set_uint8(x_367, sizeof(void*)*4, x_366);
if (lean_is_scalar(x_360)) {
 x_368 = lean_alloc_ctor(1, 4, 1);
} else {
 x_368 = x_360;
}
lean_ctor_set(x_368, 0, x_364);
lean_ctor_set(x_368, 1, x_343);
lean_ctor_set(x_368, 2, x_344);
lean_ctor_set(x_368, 3, x_345);
lean_ctor_set_uint8(x_368, sizeof(void*)*4, x_366);
x_369 = 0;
x_370 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_370, 0, x_367);
lean_ctor_set(x_370, 1, x_362);
lean_ctor_set(x_370, 2, x_363);
lean_ctor_set(x_370, 3, x_368);
lean_ctor_set_uint8(x_370, sizeof(void*)*4, x_369);
return x_370;
}
else
{
lean_object* x_371; uint8_t x_372; lean_object* x_373; 
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_371 = x_350;
} else {
 lean_dec_ref(x_350);
 x_371 = lean_box(0);
}
x_372 = 1;
if (lean_is_scalar(x_371)) {
 x_373 = lean_alloc_ctor(1, 4, 1);
} else {
 x_373 = x_371;
}
lean_ctor_set(x_373, 0, x_347);
lean_ctor_set(x_373, 1, x_343);
lean_ctor_set(x_373, 2, x_344);
lean_ctor_set(x_373, 3, x_345);
lean_ctor_set_uint8(x_373, sizeof(void*)*4, x_372);
return x_373;
}
}
}
else
{
uint8_t x_374; 
x_374 = lean_ctor_get_uint8(x_349, sizeof(void*)*4);
if (x_374 == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; uint8_t x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; lean_object* x_388; 
x_375 = lean_ctor_get(x_347, 1);
lean_inc(x_375);
x_376 = lean_ctor_get(x_347, 2);
lean_inc(x_376);
x_377 = lean_ctor_get(x_347, 3);
lean_inc(x_377);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_378 = x_347;
} else {
 lean_dec_ref(x_347);
 x_378 = lean_box(0);
}
x_379 = lean_ctor_get(x_349, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_349, 1);
lean_inc(x_380);
x_381 = lean_ctor_get(x_349, 2);
lean_inc(x_381);
x_382 = lean_ctor_get(x_349, 3);
lean_inc(x_382);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_383 = x_349;
} else {
 lean_dec_ref(x_349);
 x_383 = lean_box(0);
}
x_384 = 1;
if (lean_is_scalar(x_383)) {
 x_385 = lean_alloc_ctor(1, 4, 1);
} else {
 x_385 = x_383;
}
lean_ctor_set(x_385, 0, x_379);
lean_ctor_set(x_385, 1, x_380);
lean_ctor_set(x_385, 2, x_381);
lean_ctor_set(x_385, 3, x_382);
lean_ctor_set_uint8(x_385, sizeof(void*)*4, x_384);
if (lean_is_scalar(x_378)) {
 x_386 = lean_alloc_ctor(1, 4, 1);
} else {
 x_386 = x_378;
}
lean_ctor_set(x_386, 0, x_377);
lean_ctor_set(x_386, 1, x_343);
lean_ctor_set(x_386, 2, x_344);
lean_ctor_set(x_386, 3, x_345);
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_384);
x_387 = 0;
x_388 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_388, 0, x_385);
lean_ctor_set(x_388, 1, x_375);
lean_ctor_set(x_388, 2, x_376);
lean_ctor_set(x_388, 3, x_386);
lean_ctor_set_uint8(x_388, sizeof(void*)*4, x_387);
return x_388;
}
else
{
lean_object* x_389; 
x_389 = lean_ctor_get(x_347, 3);
lean_inc(x_389);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; uint8_t x_391; lean_object* x_392; 
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_390 = x_349;
} else {
 lean_dec_ref(x_349);
 x_390 = lean_box(0);
}
x_391 = 1;
if (lean_is_scalar(x_390)) {
 x_392 = lean_alloc_ctor(1, 4, 1);
} else {
 x_392 = x_390;
}
lean_ctor_set(x_392, 0, x_347);
lean_ctor_set(x_392, 1, x_343);
lean_ctor_set(x_392, 2, x_344);
lean_ctor_set(x_392, 3, x_345);
lean_ctor_set_uint8(x_392, sizeof(void*)*4, x_391);
return x_392;
}
else
{
uint8_t x_393; 
x_393 = lean_ctor_get_uint8(x_389, sizeof(void*)*4);
if (x_393 == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; lean_object* x_407; 
x_394 = lean_ctor_get(x_347, 1);
lean_inc(x_394);
x_395 = lean_ctor_get(x_347, 2);
lean_inc(x_395);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_396 = x_347;
} else {
 lean_dec_ref(x_347);
 x_396 = lean_box(0);
}
x_397 = lean_ctor_get(x_389, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_389, 1);
lean_inc(x_398);
x_399 = lean_ctor_get(x_389, 2);
lean_inc(x_399);
x_400 = lean_ctor_get(x_389, 3);
lean_inc(x_400);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 lean_ctor_release(x_389, 2);
 lean_ctor_release(x_389, 3);
 x_401 = x_389;
} else {
 lean_dec_ref(x_389);
 x_401 = lean_box(0);
}
x_402 = 1;
lean_inc(x_349);
if (lean_is_scalar(x_401)) {
 x_403 = lean_alloc_ctor(1, 4, 1);
} else {
 x_403 = x_401;
}
lean_ctor_set(x_403, 0, x_349);
lean_ctor_set(x_403, 1, x_394);
lean_ctor_set(x_403, 2, x_395);
lean_ctor_set(x_403, 3, x_397);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_404 = x_349;
} else {
 lean_dec_ref(x_349);
 x_404 = lean_box(0);
}
lean_ctor_set_uint8(x_403, sizeof(void*)*4, x_402);
if (lean_is_scalar(x_404)) {
 x_405 = lean_alloc_ctor(1, 4, 1);
} else {
 x_405 = x_404;
}
lean_ctor_set(x_405, 0, x_400);
lean_ctor_set(x_405, 1, x_343);
lean_ctor_set(x_405, 2, x_344);
lean_ctor_set(x_405, 3, x_345);
lean_ctor_set_uint8(x_405, sizeof(void*)*4, x_402);
x_406 = 0;
if (lean_is_scalar(x_396)) {
 x_407 = lean_alloc_ctor(1, 4, 1);
} else {
 x_407 = x_396;
}
lean_ctor_set(x_407, 0, x_403);
lean_ctor_set(x_407, 1, x_398);
lean_ctor_set(x_407, 2, x_399);
lean_ctor_set(x_407, 3, x_405);
lean_ctor_set_uint8(x_407, sizeof(void*)*4, x_406);
return x_407;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; lean_object* x_419; 
x_408 = lean_ctor_get(x_347, 1);
lean_inc(x_408);
x_409 = lean_ctor_get(x_347, 2);
lean_inc(x_409);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_410 = x_347;
} else {
 lean_dec_ref(x_347);
 x_410 = lean_box(0);
}
x_411 = lean_ctor_get(x_349, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_349, 1);
lean_inc(x_412);
x_413 = lean_ctor_get(x_349, 2);
lean_inc(x_413);
x_414 = lean_ctor_get(x_349, 3);
lean_inc(x_414);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_415 = x_349;
} else {
 lean_dec_ref(x_349);
 x_415 = lean_box(0);
}
if (lean_is_scalar(x_415)) {
 x_416 = lean_alloc_ctor(1, 4, 1);
} else {
 x_416 = x_415;
}
lean_ctor_set(x_416, 0, x_411);
lean_ctor_set(x_416, 1, x_412);
lean_ctor_set(x_416, 2, x_413);
lean_ctor_set(x_416, 3, x_414);
lean_ctor_set_uint8(x_416, sizeof(void*)*4, x_393);
if (lean_is_scalar(x_410)) {
 x_417 = lean_alloc_ctor(1, 4, 1);
} else {
 x_417 = x_410;
}
lean_ctor_set(x_417, 0, x_416);
lean_ctor_set(x_417, 1, x_408);
lean_ctor_set(x_417, 2, x_409);
lean_ctor_set(x_417, 3, x_389);
lean_ctor_set_uint8(x_417, sizeof(void*)*4, x_348);
x_418 = 1;
x_419 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_419, 0, x_417);
lean_ctor_set(x_419, 1, x_343);
lean_ctor_set(x_419, 2, x_344);
lean_ctor_set(x_419, 3, x_345);
lean_ctor_set_uint8(x_419, sizeof(void*)*4, x_418);
return x_419;
}
}
}
}
}
else
{
uint8_t x_420; lean_object* x_421; 
x_420 = 1;
x_421 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_421, 0, x_347);
lean_ctor_set(x_421, 1, x_343);
lean_ctor_set(x_421, 2, x_344);
lean_ctor_set(x_421, 3, x_345);
lean_ctor_set_uint8(x_421, sizeof(void*)*4, x_420);
return x_421;
}
}
case 1:
{
uint8_t x_422; lean_object* x_423; 
lean_dec(x_344);
lean_dec(x_343);
x_422 = 1;
x_423 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_423, 0, x_342);
lean_ctor_set(x_423, 1, x_2);
lean_ctor_set(x_423, 2, x_3);
lean_ctor_set(x_423, 3, x_345);
lean_ctor_set_uint8(x_423, sizeof(void*)*4, x_422);
return x_423;
}
default: 
{
lean_object* x_424; uint8_t x_425; 
x_424 = l_Lean_RBNode_ins___at_Lake_LeanLib_initFacetConfigs___spec__2(x_345, x_2, x_3);
x_425 = lean_ctor_get_uint8(x_424, sizeof(void*)*4);
if (x_425 == 0)
{
lean_object* x_426; 
x_426 = lean_ctor_get(x_424, 0);
lean_inc(x_426);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; 
x_427 = lean_ctor_get(x_424, 3);
lean_inc(x_427);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; uint8_t x_432; lean_object* x_433; 
x_428 = lean_ctor_get(x_424, 1);
lean_inc(x_428);
x_429 = lean_ctor_get(x_424, 2);
lean_inc(x_429);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_430 = x_424;
} else {
 lean_dec_ref(x_424);
 x_430 = lean_box(0);
}
if (lean_is_scalar(x_430)) {
 x_431 = lean_alloc_ctor(1, 4, 1);
} else {
 x_431 = x_430;
}
lean_ctor_set(x_431, 0, x_427);
lean_ctor_set(x_431, 1, x_428);
lean_ctor_set(x_431, 2, x_429);
lean_ctor_set(x_431, 3, x_427);
lean_ctor_set_uint8(x_431, sizeof(void*)*4, x_425);
x_432 = 1;
x_433 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_433, 0, x_342);
lean_ctor_set(x_433, 1, x_343);
lean_ctor_set(x_433, 2, x_344);
lean_ctor_set(x_433, 3, x_431);
lean_ctor_set_uint8(x_433, sizeof(void*)*4, x_432);
return x_433;
}
else
{
uint8_t x_434; 
x_434 = lean_ctor_get_uint8(x_427, sizeof(void*)*4);
if (x_434 == 0)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; uint8_t x_443; lean_object* x_444; lean_object* x_445; uint8_t x_446; lean_object* x_447; 
x_435 = lean_ctor_get(x_424, 1);
lean_inc(x_435);
x_436 = lean_ctor_get(x_424, 2);
lean_inc(x_436);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_437 = x_424;
} else {
 lean_dec_ref(x_424);
 x_437 = lean_box(0);
}
x_438 = lean_ctor_get(x_427, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_427, 1);
lean_inc(x_439);
x_440 = lean_ctor_get(x_427, 2);
lean_inc(x_440);
x_441 = lean_ctor_get(x_427, 3);
lean_inc(x_441);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 lean_ctor_release(x_427, 2);
 lean_ctor_release(x_427, 3);
 x_442 = x_427;
} else {
 lean_dec_ref(x_427);
 x_442 = lean_box(0);
}
x_443 = 1;
if (lean_is_scalar(x_442)) {
 x_444 = lean_alloc_ctor(1, 4, 1);
} else {
 x_444 = x_442;
}
lean_ctor_set(x_444, 0, x_342);
lean_ctor_set(x_444, 1, x_343);
lean_ctor_set(x_444, 2, x_344);
lean_ctor_set(x_444, 3, x_426);
lean_ctor_set_uint8(x_444, sizeof(void*)*4, x_443);
if (lean_is_scalar(x_437)) {
 x_445 = lean_alloc_ctor(1, 4, 1);
} else {
 x_445 = x_437;
}
lean_ctor_set(x_445, 0, x_438);
lean_ctor_set(x_445, 1, x_439);
lean_ctor_set(x_445, 2, x_440);
lean_ctor_set(x_445, 3, x_441);
lean_ctor_set_uint8(x_445, sizeof(void*)*4, x_443);
x_446 = 0;
x_447 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_447, 0, x_444);
lean_ctor_set(x_447, 1, x_435);
lean_ctor_set(x_447, 2, x_436);
lean_ctor_set(x_447, 3, x_445);
lean_ctor_set_uint8(x_447, sizeof(void*)*4, x_446);
return x_447;
}
else
{
lean_object* x_448; uint8_t x_449; lean_object* x_450; 
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 lean_ctor_release(x_427, 2);
 lean_ctor_release(x_427, 3);
 x_448 = x_427;
} else {
 lean_dec_ref(x_427);
 x_448 = lean_box(0);
}
x_449 = 1;
if (lean_is_scalar(x_448)) {
 x_450 = lean_alloc_ctor(1, 4, 1);
} else {
 x_450 = x_448;
}
lean_ctor_set(x_450, 0, x_342);
lean_ctor_set(x_450, 1, x_343);
lean_ctor_set(x_450, 2, x_344);
lean_ctor_set(x_450, 3, x_424);
lean_ctor_set_uint8(x_450, sizeof(void*)*4, x_449);
return x_450;
}
}
}
else
{
uint8_t x_451; 
x_451 = lean_ctor_get_uint8(x_426, sizeof(void*)*4);
if (x_451 == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; uint8_t x_461; lean_object* x_462; lean_object* x_463; uint8_t x_464; lean_object* x_465; 
x_452 = lean_ctor_get(x_424, 1);
lean_inc(x_452);
x_453 = lean_ctor_get(x_424, 2);
lean_inc(x_453);
x_454 = lean_ctor_get(x_424, 3);
lean_inc(x_454);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_455 = x_424;
} else {
 lean_dec_ref(x_424);
 x_455 = lean_box(0);
}
x_456 = lean_ctor_get(x_426, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_426, 1);
lean_inc(x_457);
x_458 = lean_ctor_get(x_426, 2);
lean_inc(x_458);
x_459 = lean_ctor_get(x_426, 3);
lean_inc(x_459);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_460 = x_426;
} else {
 lean_dec_ref(x_426);
 x_460 = lean_box(0);
}
x_461 = 1;
if (lean_is_scalar(x_460)) {
 x_462 = lean_alloc_ctor(1, 4, 1);
} else {
 x_462 = x_460;
}
lean_ctor_set(x_462, 0, x_342);
lean_ctor_set(x_462, 1, x_343);
lean_ctor_set(x_462, 2, x_344);
lean_ctor_set(x_462, 3, x_456);
lean_ctor_set_uint8(x_462, sizeof(void*)*4, x_461);
if (lean_is_scalar(x_455)) {
 x_463 = lean_alloc_ctor(1, 4, 1);
} else {
 x_463 = x_455;
}
lean_ctor_set(x_463, 0, x_459);
lean_ctor_set(x_463, 1, x_452);
lean_ctor_set(x_463, 2, x_453);
lean_ctor_set(x_463, 3, x_454);
lean_ctor_set_uint8(x_463, sizeof(void*)*4, x_461);
x_464 = 0;
x_465 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_465, 0, x_462);
lean_ctor_set(x_465, 1, x_457);
lean_ctor_set(x_465, 2, x_458);
lean_ctor_set(x_465, 3, x_463);
lean_ctor_set_uint8(x_465, sizeof(void*)*4, x_464);
return x_465;
}
else
{
lean_object* x_466; 
x_466 = lean_ctor_get(x_424, 3);
lean_inc(x_466);
if (lean_obj_tag(x_466) == 0)
{
lean_object* x_467; uint8_t x_468; lean_object* x_469; 
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_467 = x_426;
} else {
 lean_dec_ref(x_426);
 x_467 = lean_box(0);
}
x_468 = 1;
if (lean_is_scalar(x_467)) {
 x_469 = lean_alloc_ctor(1, 4, 1);
} else {
 x_469 = x_467;
}
lean_ctor_set(x_469, 0, x_342);
lean_ctor_set(x_469, 1, x_343);
lean_ctor_set(x_469, 2, x_344);
lean_ctor_set(x_469, 3, x_424);
lean_ctor_set_uint8(x_469, sizeof(void*)*4, x_468);
return x_469;
}
else
{
uint8_t x_470; 
x_470 = lean_ctor_get_uint8(x_466, sizeof(void*)*4);
if (x_470 == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; uint8_t x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; uint8_t x_483; lean_object* x_484; 
x_471 = lean_ctor_get(x_424, 1);
lean_inc(x_471);
x_472 = lean_ctor_get(x_424, 2);
lean_inc(x_472);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_473 = x_424;
} else {
 lean_dec_ref(x_424);
 x_473 = lean_box(0);
}
x_474 = lean_ctor_get(x_466, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_466, 1);
lean_inc(x_475);
x_476 = lean_ctor_get(x_466, 2);
lean_inc(x_476);
x_477 = lean_ctor_get(x_466, 3);
lean_inc(x_477);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 lean_ctor_release(x_466, 1);
 lean_ctor_release(x_466, 2);
 lean_ctor_release(x_466, 3);
 x_478 = x_466;
} else {
 lean_dec_ref(x_466);
 x_478 = lean_box(0);
}
x_479 = 1;
lean_inc(x_426);
if (lean_is_scalar(x_478)) {
 x_480 = lean_alloc_ctor(1, 4, 1);
} else {
 x_480 = x_478;
}
lean_ctor_set(x_480, 0, x_342);
lean_ctor_set(x_480, 1, x_343);
lean_ctor_set(x_480, 2, x_344);
lean_ctor_set(x_480, 3, x_426);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_481 = x_426;
} else {
 lean_dec_ref(x_426);
 x_481 = lean_box(0);
}
lean_ctor_set_uint8(x_480, sizeof(void*)*4, x_479);
if (lean_is_scalar(x_481)) {
 x_482 = lean_alloc_ctor(1, 4, 1);
} else {
 x_482 = x_481;
}
lean_ctor_set(x_482, 0, x_474);
lean_ctor_set(x_482, 1, x_475);
lean_ctor_set(x_482, 2, x_476);
lean_ctor_set(x_482, 3, x_477);
lean_ctor_set_uint8(x_482, sizeof(void*)*4, x_479);
x_483 = 0;
if (lean_is_scalar(x_473)) {
 x_484 = lean_alloc_ctor(1, 4, 1);
} else {
 x_484 = x_473;
}
lean_ctor_set(x_484, 0, x_480);
lean_ctor_set(x_484, 1, x_471);
lean_ctor_set(x_484, 2, x_472);
lean_ctor_set(x_484, 3, x_482);
lean_ctor_set_uint8(x_484, sizeof(void*)*4, x_483);
return x_484;
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; uint8_t x_495; lean_object* x_496; 
x_485 = lean_ctor_get(x_424, 1);
lean_inc(x_485);
x_486 = lean_ctor_get(x_424, 2);
lean_inc(x_486);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_487 = x_424;
} else {
 lean_dec_ref(x_424);
 x_487 = lean_box(0);
}
x_488 = lean_ctor_get(x_426, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_426, 1);
lean_inc(x_489);
x_490 = lean_ctor_get(x_426, 2);
lean_inc(x_490);
x_491 = lean_ctor_get(x_426, 3);
lean_inc(x_491);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_492 = x_426;
} else {
 lean_dec_ref(x_426);
 x_492 = lean_box(0);
}
if (lean_is_scalar(x_492)) {
 x_493 = lean_alloc_ctor(1, 4, 1);
} else {
 x_493 = x_492;
}
lean_ctor_set(x_493, 0, x_488);
lean_ctor_set(x_493, 1, x_489);
lean_ctor_set(x_493, 2, x_490);
lean_ctor_set(x_493, 3, x_491);
lean_ctor_set_uint8(x_493, sizeof(void*)*4, x_470);
if (lean_is_scalar(x_487)) {
 x_494 = lean_alloc_ctor(1, 4, 1);
} else {
 x_494 = x_487;
}
lean_ctor_set(x_494, 0, x_493);
lean_ctor_set(x_494, 1, x_485);
lean_ctor_set(x_494, 2, x_486);
lean_ctor_set(x_494, 3, x_466);
lean_ctor_set_uint8(x_494, sizeof(void*)*4, x_425);
x_495 = 1;
x_496 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_496, 0, x_342);
lean_ctor_set(x_496, 1, x_343);
lean_ctor_set(x_496, 2, x_344);
lean_ctor_set(x_496, 3, x_494);
lean_ctor_set_uint8(x_496, sizeof(void*)*4, x_495);
return x_496;
}
}
}
}
}
else
{
uint8_t x_497; lean_object* x_498; 
x_497 = 1;
x_498 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_498, 0, x_342);
lean_ctor_set(x_498, 1, x_343);
lean_ctor_set(x_498, 2, x_344);
lean_ctor_set(x_498, 3, x_424);
lean_ctor_set_uint8(x_498, sizeof(void*)*4, x_497);
return x_498;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lake_LeanLib_initFacetConfigs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_ins___at_Lake_LeanLib_initFacetConfigs___spec__2(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_RBNode_ins___at_Lake_LeanLib_initFacetConfigs___spec__2(x_1, x_2, x_3);
x_7 = l_Lean_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanLib_defaultFacet;
x_3 = l_Lake_LeanLib_defaultFacetConfig;
x_4 = l_Lean_RBNode_insert___at_Lake_LeanLib_initFacetConfigs___spec__1(x_1, x_2, x_3);
x_5 = l_Lake_LeanLib_modulesFacet;
x_6 = l_Lake_LeanLib_modulesFacetConfig;
x_7 = l_Lean_RBNode_insert___at_Lake_LeanLib_initFacetConfigs___spec__1(x_4, x_5, x_6);
x_8 = l_Lake_LeanLib_leanArtsFacet;
x_9 = l_Lake_LeanLib_leanArtsFacetConfig;
x_10 = l_Lean_RBNode_insert___at_Lake_LeanLib_initFacetConfigs___spec__1(x_7, x_8, x_9);
x_11 = l_Lake_LeanLib_staticFacet;
x_12 = l_Lake_LeanLib_staticFacetConfig;
x_13 = l_Lean_RBNode_insert___at_Lake_LeanLib_initFacetConfigs___spec__1(x_10, x_11, x_12);
x_14 = l_Lake_LeanLib_staticExportFacet;
x_15 = l_Lake_LeanLib_staticExportFacetConfig;
x_16 = l_Lean_RBNode_insert___at_Lake_LeanLib_initFacetConfigs___spec__1(x_13, x_14, x_15);
x_17 = l_Lake_LeanLib_sharedFacet;
x_18 = l_Lake_LeanLib_sharedFacetConfig;
x_19 = l_Lean_RBNode_insert___at_Lake_LeanLib_initFacetConfigs___spec__1(x_16, x_17, x_18);
x_20 = l_Lake_LeanLib_extraDepFacet;
x_21 = l_Lake_LeanLib_extraDepFacetConfig;
x_22 = l_Lean_RBNode_insert___at_Lake_LeanLib_initFacetConfigs___spec__1(x_19, x_20, x_21);
return x_22;
}
}
static lean_object* _init_l_Lake_initLibraryFacetConfigs() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_LeanLib_initFacetConfigs;
return x_1;
}
}
lean_object* initialize_Lake_Build_Common(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Targets(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Library(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Common(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Targets(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_LeanLib_recCollectLocalModules_go___closed__1 = _init_l_Lake_LeanLib_recCollectLocalModules_go___closed__1();
lean_mark_persistent(l_Lake_LeanLib_recCollectLocalModules_go___closed__1);
l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__1 = _init_l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__1();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__1);
l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__2 = _init_l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__2();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__2);
l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__3 = _init_l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__3();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__3);
l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__4 = _init_l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__4();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__4);
l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__5 = _init_l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__5();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lake_LeanLib_recCollectLocalModules___spec__4___closed__5);
l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__1 = _init_l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__1();
lean_mark_persistent(l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__1);
l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__2 = _init_l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__2();
lean_mark_persistent(l_Lake_ensureJob___at_Lake_LeanLib_recCollectLocalModules___spec__3___closed__2);
l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__1 = _init_l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__1();
lean_mark_persistent(l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__1);
l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__2 = _init_l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__2();
lean_mark_persistent(l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__2);
l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__3 = _init_l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__3();
lean_mark_persistent(l_Lake_LeanLib_recCollectLocalModules___lambda__2___closed__3);
l_Lake_LeanLib_recCollectLocalModules___closed__1 = _init_l_Lake_LeanLib_recCollectLocalModules___closed__1();
lean_mark_persistent(l_Lake_LeanLib_recCollectLocalModules___closed__1);
l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___spec__2___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___spec__2___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___spec__2___closed__1);
l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___spec__2___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___spec__2___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_LeanLib_modulesFacetConfig___spec__2___closed__2);
l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__1 = _init_l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__1();
lean_mark_persistent(l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__1);
l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__2 = _init_l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__2();
lean_mark_persistent(l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__2);
l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__3 = _init_l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__3();
lean_mark_persistent(l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__3);
l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__4 = _init_l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__4();
lean_mark_persistent(l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__4);
l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__5 = _init_l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__5();
lean_mark_persistent(l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__5);
l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__6 = _init_l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__6();
lean_mark_persistent(l_Lake_stdFormat___at_Lake_LeanLib_modulesFacetConfig___spec__1___closed__6);
l_Lake_LeanLib_modulesFacetConfig___closed__1 = _init_l_Lake_LeanLib_modulesFacetConfig___closed__1();
lean_mark_persistent(l_Lake_LeanLib_modulesFacetConfig___closed__1);
l_Lake_LeanLib_modulesFacetConfig___closed__2 = _init_l_Lake_LeanLib_modulesFacetConfig___closed__2();
lean_mark_persistent(l_Lake_LeanLib_modulesFacetConfig___closed__2);
l_Lake_LeanLib_modulesFacetConfig___closed__3 = _init_l_Lake_LeanLib_modulesFacetConfig___closed__3();
lean_mark_persistent(l_Lake_LeanLib_modulesFacetConfig___closed__3);
l_Lake_LeanLib_modulesFacetConfig___closed__4 = _init_l_Lake_LeanLib_modulesFacetConfig___closed__4();
lean_mark_persistent(l_Lake_LeanLib_modulesFacetConfig___closed__4);
l_Lake_LeanLib_modulesFacetConfig___closed__5 = _init_l_Lake_LeanLib_modulesFacetConfig___closed__5();
lean_mark_persistent(l_Lake_LeanLib_modulesFacetConfig___closed__5);
l_Lake_LeanLib_modulesFacetConfig = _init_l_Lake_LeanLib_modulesFacetConfig();
lean_mark_persistent(l_Lake_LeanLib_modulesFacetConfig);
l_Lake_LeanLib_recBuildLean___closed__1 = _init_l_Lake_LeanLib_recBuildLean___closed__1();
lean_mark_persistent(l_Lake_LeanLib_recBuildLean___closed__1);
l_Lake_LeanLib_recBuildLean___closed__2 = _init_l_Lake_LeanLib_recBuildLean___closed__2();
lean_mark_persistent(l_Lake_LeanLib_recBuildLean___closed__2);
l_Lake_LeanLib_recBuildLean___closed__3 = _init_l_Lake_LeanLib_recBuildLean___closed__3();
lean_mark_persistent(l_Lake_LeanLib_recBuildLean___closed__3);
l_Lake_LeanLib_recBuildLean___closed__4 = _init_l_Lake_LeanLib_recBuildLean___closed__4();
lean_mark_persistent(l_Lake_LeanLib_recBuildLean___closed__4);
l_Lake_LeanLib_leanArtsFacetConfig___closed__1 = _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__1();
lean_mark_persistent(l_Lake_LeanLib_leanArtsFacetConfig___closed__1);
l_Lake_LeanLib_leanArtsFacetConfig___closed__2 = _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__2();
lean_mark_persistent(l_Lake_LeanLib_leanArtsFacetConfig___closed__2);
l_Lake_LeanLib_leanArtsFacetConfig___closed__3 = _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__3();
lean_mark_persistent(l_Lake_LeanLib_leanArtsFacetConfig___closed__3);
l_Lake_LeanLib_leanArtsFacetConfig = _init_l_Lake_LeanLib_leanArtsFacetConfig();
lean_mark_persistent(l_Lake_LeanLib_leanArtsFacetConfig);
l_Lake_LeanLib_recBuildStatic___lambda__4___closed__1 = _init_l_Lake_LeanLib_recBuildStatic___lambda__4___closed__1();
lean_mark_persistent(l_Lake_LeanLib_recBuildStatic___lambda__4___closed__1);
l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2 = _init_l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2();
lean_mark_persistent(l_Lake_LeanLib_recBuildStatic___lambda__4___closed__2);
l_Lake_LeanLib_recBuildStatic___lambda__4___closed__3 = _init_l_Lake_LeanLib_recBuildStatic___lambda__4___closed__3();
lean_mark_persistent(l_Lake_LeanLib_recBuildStatic___lambda__4___closed__3);
l_Lake_LeanLib_recBuildStatic___closed__1 = _init_l_Lake_LeanLib_recBuildStatic___closed__1();
lean_mark_persistent(l_Lake_LeanLib_recBuildStatic___closed__1);
l_Lake_LeanLib_recBuildStatic___closed__2 = _init_l_Lake_LeanLib_recBuildStatic___closed__2();
lean_mark_persistent(l_Lake_LeanLib_recBuildStatic___closed__2);
l_Lake_LeanLib_recBuildStatic___closed__3 = _init_l_Lake_LeanLib_recBuildStatic___closed__3();
lean_mark_persistent(l_Lake_LeanLib_recBuildStatic___closed__3);
l_Lake_LeanLib_recBuildStatic___closed__4 = _init_l_Lake_LeanLib_recBuildStatic___closed__4();
lean_mark_persistent(l_Lake_LeanLib_recBuildStatic___closed__4);
l_Lake_LeanLib_recBuildStatic___closed__5 = _init_l_Lake_LeanLib_recBuildStatic___closed__5();
lean_mark_persistent(l_Lake_LeanLib_recBuildStatic___closed__5);
l_Lake_LeanLib_recBuildStatic___closed__6 = _init_l_Lake_LeanLib_recBuildStatic___closed__6();
lean_mark_persistent(l_Lake_LeanLib_recBuildStatic___closed__6);
l_Lake_LeanLib_recBuildStatic___closed__7 = _init_l_Lake_LeanLib_recBuildStatic___closed__7();
lean_mark_persistent(l_Lake_LeanLib_recBuildStatic___closed__7);
l_Lake_LeanLib_staticFacetConfig___closed__1 = _init_l_Lake_LeanLib_staticFacetConfig___closed__1();
lean_mark_persistent(l_Lake_LeanLib_staticFacetConfig___closed__1);
l_Lake_LeanLib_staticFacetConfig___closed__2 = _init_l_Lake_LeanLib_staticFacetConfig___closed__2();
lean_mark_persistent(l_Lake_LeanLib_staticFacetConfig___closed__2);
l_Lake_LeanLib_staticFacetConfig___closed__3 = _init_l_Lake_LeanLib_staticFacetConfig___closed__3();
lean_mark_persistent(l_Lake_LeanLib_staticFacetConfig___closed__3);
l_Lake_LeanLib_staticFacetConfig = _init_l_Lake_LeanLib_staticFacetConfig();
lean_mark_persistent(l_Lake_LeanLib_staticFacetConfig);
l_Lake_LeanLib_staticExportFacetConfig___closed__1 = _init_l_Lake_LeanLib_staticExportFacetConfig___closed__1();
lean_mark_persistent(l_Lake_LeanLib_staticExportFacetConfig___closed__1);
l_Lake_LeanLib_staticExportFacetConfig___closed__2 = _init_l_Lake_LeanLib_staticExportFacetConfig___closed__2();
lean_mark_persistent(l_Lake_LeanLib_staticExportFacetConfig___closed__2);
l_Lake_LeanLib_staticExportFacetConfig = _init_l_Lake_LeanLib_staticExportFacetConfig();
lean_mark_persistent(l_Lake_LeanLib_staticExportFacetConfig);
l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__1 = _init_l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__1();
lean_mark_persistent(l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__1);
l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__2 = _init_l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__2();
lean_mark_persistent(l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__2);
l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__3 = _init_l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__3();
lean_mark_persistent(l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__3);
l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__4 = _init_l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__4();
lean_mark_persistent(l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__4);
l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__5 = _init_l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__5();
lean_mark_persistent(l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__5);
l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__6 = _init_l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__6();
lean_mark_persistent(l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__1___closed__6);
l_Lake_OrdHashSet_insert___at_Lake_LeanLib_recBuildShared___spec__9___closed__1 = _init_l_Lake_OrdHashSet_insert___at_Lake_LeanLib_recBuildShared___spec__9___closed__1();
lean_mark_persistent(l_Lake_OrdHashSet_insert___at_Lake_LeanLib_recBuildShared___spec__9___closed__1);
l_Lake_OrdHashSet_insert___at_Lake_LeanLib_recBuildShared___spec__9___closed__2 = _init_l_Lake_OrdHashSet_insert___at_Lake_LeanLib_recBuildShared___spec__9___closed__2();
lean_mark_persistent(l_Lake_OrdHashSet_insert___at_Lake_LeanLib_recBuildShared___spec__9___closed__2);
l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__12___closed__1 = _init_l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__12___closed__1();
lean_mark_persistent(l_Lake_Target_fetchIn___at_Lake_LeanLib_recBuildShared___spec__12___closed__1);
l_Lake_LeanLib_recBuildShared___closed__1 = _init_l_Lake_LeanLib_recBuildShared___closed__1();
lean_mark_persistent(l_Lake_LeanLib_recBuildShared___closed__1);
l_Lake_LeanLib_sharedFacetConfig___closed__1 = _init_l_Lake_LeanLib_sharedFacetConfig___closed__1();
lean_mark_persistent(l_Lake_LeanLib_sharedFacetConfig___closed__1);
l_Lake_LeanLib_sharedFacetConfig___closed__2 = _init_l_Lake_LeanLib_sharedFacetConfig___closed__2();
lean_mark_persistent(l_Lake_LeanLib_sharedFacetConfig___closed__2);
l_Lake_LeanLib_sharedFacetConfig___closed__3 = _init_l_Lake_LeanLib_sharedFacetConfig___closed__3();
lean_mark_persistent(l_Lake_LeanLib_sharedFacetConfig___closed__3);
l_Lake_LeanLib_sharedFacetConfig = _init_l_Lake_LeanLib_sharedFacetConfig();
lean_mark_persistent(l_Lake_LeanLib_sharedFacetConfig);
l_Lake_LeanLib_extraDepFacetConfig___closed__1 = _init_l_Lake_LeanLib_extraDepFacetConfig___closed__1();
lean_mark_persistent(l_Lake_LeanLib_extraDepFacetConfig___closed__1);
l_Lake_LeanLib_extraDepFacetConfig___closed__2 = _init_l_Lake_LeanLib_extraDepFacetConfig___closed__2();
lean_mark_persistent(l_Lake_LeanLib_extraDepFacetConfig___closed__2);
l_Lake_LeanLib_extraDepFacetConfig = _init_l_Lake_LeanLib_extraDepFacetConfig();
lean_mark_persistent(l_Lake_LeanLib_extraDepFacetConfig);
l_Lake_LeanLib_defaultFacetConfig___closed__1 = _init_l_Lake_LeanLib_defaultFacetConfig___closed__1();
lean_mark_persistent(l_Lake_LeanLib_defaultFacetConfig___closed__1);
l_Lake_LeanLib_defaultFacetConfig___closed__2 = _init_l_Lake_LeanLib_defaultFacetConfig___closed__2();
lean_mark_persistent(l_Lake_LeanLib_defaultFacetConfig___closed__2);
l_Lake_LeanLib_defaultFacetConfig = _init_l_Lake_LeanLib_defaultFacetConfig();
lean_mark_persistent(l_Lake_LeanLib_defaultFacetConfig);
l_Lake_LeanLib_initFacetConfigs = _init_l_Lake_LeanLib_initFacetConfigs();
lean_mark_persistent(l_Lake_LeanLib_initFacetConfigs);
l_Lake_initLibraryFacetConfigs = _init_l_Lake_initLibraryFacetConfigs();
lean_mark_persistent(l_Lake_initLibraryFacetConfigs);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
